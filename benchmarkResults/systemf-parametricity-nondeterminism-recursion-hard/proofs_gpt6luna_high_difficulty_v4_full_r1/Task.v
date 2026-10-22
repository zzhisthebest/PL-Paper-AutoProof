(** System F parametricity benchmark, Hard variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia Program.Equality.
Import ListNotations.

Module SystemFParametricityNondeterminismRecursionHardTask.

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
  | tm_natrec : tm -> tm -> tm -> tm
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

Notation "'Nat'" := Ty_Nat (in custom systemf_ty at level 0) : systemf_scope.
Notation "'zero'" := tm_zero (in custom systemf_tm at level 0) : systemf_scope.
Notation "'succ' t" := (tm_succ t) (in custom systemf_tm at level 9, t custom systemf_tm at level 0) : systemf_scope.
Notation "'rec' n b s" := (tm_natrec n b s)
  (in custom systemf_tm at level 9, n custom systemf_tm at level 0, b custom systemf_tm at level 0, s custom systemf_tm at level 0) : systemf_scope.
Notation "'choice' t1 'or' t2" := (tm_choice t1 t2)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm at level 200) : systemf_scope.

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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (open_tm_ty_rec k U t1)
  | tm_natrec n b f => tm_natrec (open_tm_ty_rec k U n) (open_tm_ty_rec k U b) (open_tm_ty_rec k U f)
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
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_subst x s t1)
  | tm_natrec n b f => tm_natrec (tm_subst x s n) (tm_subst x s b) (tm_subst x s f)
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
      lc_tm_at K k n -> lc_tm_at K k b -> lc_tm_at K k s -> lc_tm_at K k (tm_natrec n b s)
  | lc_tm_choice : forall K k t1 t2,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k (tm_choice t1 t2).

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
      has_type Delta Gamma (tm_natrec n b s) T
  | T_Choice : forall Delta Gamma t1 t2 T,
      has_type Delta Gamma t1 T -> has_type Delta Gamma t2 T ->
      has_type Delta Gamma (tm_choice t1 t2) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).


Hint Constructors lc_ty_at lc_tm_at value : core.

(* A binary, step-index-free logical relation.  Expressions are related when
   they can evaluate to related values; the value relation is indexed by a
   pair of types and by a relation interpreting free type variables. *)
Definition term_rel := tm -> tm -> Prop.
Definition ty_rel_env := atom -> term_rel.
Definition update_ty_rel_env (xi : ty_rel_env) (X : atom) (R : term_rel)
  : ty_rel_env := fun Y => if Nat.eqb Y X then R else xi Y.

Fixpoint rel_ty (xi : ty_rel_env) (rho : list term_rel)
    (T1 T2 : ty) : term_rel :=
  match T1, T2 with
  | Ty_Nat, Ty_Nat => fun v1 v2 => exists n, v1 = numeral n /\ v2 = numeral n
  | Ty_BVar i, Ty_BVar j => fun v1 v2 => nth i rho (fun _ _ => False) v1 v2
  | Ty_FVar X, Ty_FVar Y => fun v1 v2 => xi X v1 v2
  | Ty_Arrow A1 B1, Ty_Arrow A2 B2 => fun v1 v2 =>
      value v1 /\ value v2 /\
      (forall a1 a2, (exists x1 x2, multi a1 x1 /\ multi a2 x2 /\
           value x1 /\ value x2 /\ rel_ty xi rho A1 A2 x1 x2) ->
        exists y1 y2, multi (tm_app v1 a1) y1 /\ multi (tm_app v2 a2) y2 /\
          value y1 /\ value y2 /\ rel_ty xi rho B1 B2 y1 y2)
  | Ty_All A1, Ty_All A2 => fun v1 v2 =>
      value v1 /\ value v2 /\
      (forall U1 U2 (R : term_rel),
        locally_closed_ty U1 -> locally_closed_ty U2 ->
        (forall x y, R x y -> value x /\ value y) ->
        exists y1 y2, multi (tm_tapp v1 U1) y1 /\ multi (tm_tapp v2 U2) y2 /\
          value y1 /\ value y2 /\ rel_ty xi (R :: rho) A1 A2 y1 y2)
  | _, _ => fun _ _ => False
  end.

Definition exp_rel (xi : ty_rel_env) (rho : list term_rel)
    (T1 T2 : ty) (t1 t2 : tm) : Prop :=
  exists v1 v2, multi t1 v1 /\ multi t2 v2 /\ value v1 /\ value v2 /\
    rel_ty xi rho T1 T2 v1 v2.

Fixpoint ftv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ | Ty_Nat => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ftv_ty A ++ ftv_ty B
  | Ty_All A => ftv_ty A
  end.

Lemma not_in_app_left : forall (x : atom) xs ys,
  ~ In x (xs ++ ys) -> ~ In x xs.
Proof. intros x xs ys H Hin; apply H; apply in_or_app; left; exact Hin. Qed.

Lemma not_in_app_right : forall (x : atom) xs ys,
  ~ In x (xs ++ ys) -> ~ In x ys.
Proof. intros x xs ys H Hin; apply H; apply in_or_app; right; exact Hin. Qed.

Lemma exp_rel_equiv : forall xi1 xi2 rho1 rho2 A1 A2 B1 B2 t1 t2,
  (forall v1 v2, rel_ty xi1 rho1 A1 A2 v1 v2 <->
                 rel_ty xi2 rho2 B1 B2 v1 v2) ->
  (exp_rel xi1 rho1 A1 A2 t1 t2 <-> exp_rel xi2 rho2 B1 B2 t1 t2).
Proof.
  intros xi1 xi2 rho1 rho2 A1 A2 B1 B2 t1 t2 Heq; unfold exp_rel.
  split; intros [v1 [v2 [H1 [H2 [Hv1 [Hv2 Hr]]]]]];
    exists v1, v2; repeat split; auto; apply Heq; exact Hr.
Qed.

Lemma rel_ty_update_irrelevant : forall A1 A2 xi X R rho,
  ~ In X (ftv_ty A1 ++ ftv_ty A2) -> forall v1 v2,
  rel_ty (update_ty_rel_env xi X R) rho A1 A2 v1 v2 <->
  rel_ty xi rho A1 A2 v1 v2.
Proof.
  induction A1 as [i|Y|A11 IHA11 B11 IHB11|A11 IHA11|];
    intros A2 xi X R rho Hfresh v1 v2;
    destruct A2 as [j|Z|A21 B21|A21|]; simpl in *; try tauto.
  - destruct (Nat.eqb Y X) eqn:E.
    + apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; simpl; auto.
    + unfold update_ty_rel_env; rewrite E; reflexivity.
  - assert (HA : ~ In X (ftv_ty A11 ++ ftv_ty A21)) by
      (intro Hin; apply Hfresh; repeat rewrite in_app_iff in *; tauto).
    assert (HB : ~ In X (ftv_ty B11 ++ ftv_ty B21)) by
      (intro Hin; apply Hfresh; repeat rewrite in_app_iff in *; tauto).
    split.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Harg.
      assert (Harg' : exp_rel (update_ty_rel_env xi X R) rho A11 A21 a1 a2).
      { apply (proj2 (exp_rel_equiv _ _ _ _ _ _ _ _ _ _
          (fun x y => IHA11 A21 xi X R rho HA x y))); exact Harg. }
      specialize (Hfun a1 a2 Harg') as [b1 [b2 [Hb1 [Hb2 [Hbv1 [Hbv2 Hbr]]]]]].
      exists b1, b2; repeat split; auto.
      apply (proj1 (IHB11 B21 xi X R rho HB b1 b2)); exact Hbr.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Harg.
      assert (Harg' : exp_rel xi rho A11 A21 a1 a2).
      { apply (proj1 (exp_rel_equiv _ _ _ _ _ _ _ _ _ _
          (fun x y => IHA11 A21 xi X R rho HA x y))); exact Harg. }
      specialize (Hfun a1 a2 Harg') as [b1 [b2 [Hb1 [Hb2 [Hbv1 [Hbv2 Hbr]]]]]].
      exists b1, b2; repeat split; auto.
      apply (proj2 (IHB11 B21 xi X R rho HB b1 b2)); exact Hbr.
  - split.
    + intros [Hv1 [Hv2 Hall]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 Q HU1 HU2 HQ.
      specialize (Hall U1 U2 Q HU1 HU2 HQ) as [w1 [w2 [Hw1 [Hw2 [Hwv1 [Hwv2 Hwr]]]]]].
      exists w1, w2; repeat split; auto.
      apply (IHA11 A21 xi X R (Q :: rho) Hfresh w1 w2); exact Hwr.
    + intros [Hv1 [Hv2 Hall]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 Q HU1 HU2 HQ.
      specialize (Hall U1 U2 Q HU1 HU2 HQ) as [w1 [w2 [Hw1 [Hw2 [Hwv1 [Hwv2 Hwr]]]]]].
      exists w1, w2; repeat split; auto.
      apply (IHA11 A21 xi X R (Q :: rho) Hfresh w1 w2); exact Hwr.
Qed.

Lemma rel_open_ty_rec : forall T d xi X R rho,
  length rho = d ->
  lc_ty_at (S d) T ->
  ~ In X (ftv_ty T) ->
  forall v1 v2,
    rel_ty (update_ty_rel_env xi X R) rho
      (open_ty_rec d (Ty_FVar X) T) (open_ty_rec d (Ty_FVar X) T) v1 v2 <->
    rel_ty xi (rho ++ [R]) T T v1 v2.
Proof.
  intros T d xi X R rho Hlen Hlc Hfresh.
  revert d xi X R rho Hlen Hlc Hfresh; induction T;
    intros d xi X R rho Hlen Hlc Hfresh v1 v2; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb (length rho) n) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      unfold update_ty_rel_env; simpl; rewrite Nat.eqb_refl.
      rewrite nth_middle; reflexivity.
    + assert (Hlt : n < length rho) by (apply Nat.eqb_neq in E; lia).
      rewrite app_nth1 by exact Hlt.
      unfold update_ty_rel_env; simpl.
      reflexivity.
  - destruct (Nat.eqb a X) eqn:E.
    + apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; simpl; auto.
    + unfold update_ty_rel_env; rewrite E; reflexivity.
  - inversion Hlc; subst.
    assert (HA : ~ In X (ftv_ty T1)) by (apply not_in_app_left with (ys := ftv_ty T2); exact Hfresh).
    assert (HB : ~ In X (ftv_ty T2)) by (apply not_in_app_right with (xs := ftv_ty T1); exact Hfresh).
    simpl.
    assert (HrelA : forall x y,
      rel_ty (update_ty_rel_env xi X R) rho
        (open_ty_rec (length rho) (Ty_FVar X) T1)
        (open_ty_rec (length rho) (Ty_FVar X) T1) x y <->
      rel_ty xi (rho ++ [R]) T1 T1 x y).
    { intros x y; apply IHT1 with (d := length rho) (xi := xi) (X := X)
        (R := R) (rho := rho); auto; inversion Hlc; assumption. }
    assert (HrelB : forall x y,
      rel_ty (update_ty_rel_env xi X R) rho
        (open_ty_rec (length rho) (Ty_FVar X) T2)
        (open_ty_rec (length rho) (Ty_FVar X) T2) x y <->
      rel_ty xi (rho ++ [R]) T2 T2 x y).
    { intros x y; apply IHT2 with (d := length rho) (xi := xi) (X := X)
        (R := R) (rho := rho); auto; inversion Hlc; assumption. }
    split.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Harg.
      assert (Harg' : exp_rel (update_ty_rel_env xi X R) rho
        (open_ty_rec (length rho) (Ty_FVar X) T1)
        (open_ty_rec (length rho) (Ty_FVar X) T1) a1 a2).
      { apply (proj2 (exp_rel_equiv _ _ _ _ _ _ _ _ _ _ HrelA)); exact Harg. }
      specialize (Hfun a1 a2 Harg') as [b1 [b2 [Hb1 [Hb2 [Hbv1 [Hbv2 Hbr]]]]]].
      exists b1, b2; repeat split; auto.
      apply (proj1 (HrelB b1 b2)); exact Hbr.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Harg.
      assert (Harg' : exp_rel xi (rho ++ [R]) T1 T1 a1 a2).
      { apply (proj1 (exp_rel_equiv _ _ _ _ _ _ _ _ _ _ HrelA)); exact Harg. }
      specialize (Hfun a1 a2 Harg') as [b1 [b2 [Hb1 [Hb2 [Hbv1 [Hbv2 Hbr]]]]]].
      exists b1, b2; repeat split; auto.
      apply (proj2 (HrelB b1 b2)); exact Hbr.
  - inversion Hlc; subst.
    simpl.
    split.
    + intros [Hv1 [Hv2 Hall]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 Q HU1 HU2 HQ.
      specialize (Hall U1 U2 Q HU1 HU2 HQ) as [w1 [w2 [Hw1 [Hw2 [Hwv1 [Hwv2 Hwr]]]]]].
      exists w1, w2; repeat split; auto.
      assert (Hbody : forall x y,
        rel_ty (update_ty_rel_env xi X R) (Q :: rho)
          (open_ty_rec (S (length rho)) (Ty_FVar X) T)
          (open_ty_rec (S (length rho)) (Ty_FVar X) T) x y <->
        rel_ty xi ((Q :: rho) ++ [R]) T T x y).
      { intros x y; apply IHT with (d := S (length rho)) (xi := xi)
          (X := X) (R := R) (rho := Q :: rho); simpl; auto. }
      apply (proj1 (Hbody w1 w2)); exact Hwr.
    + intros [Hv1 [Hv2 Hall]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros U1 U2 Q HU1 HU2 HQ.
      specialize (Hall U1 U2 Q HU1 HU2 HQ) as [w1 [w2 [Hw1 [Hw2 [Hwv1 [Hwv2 Hwr]]]]]].
      exists w1, w2; repeat split; auto.
      assert (Hbody : forall x y,
        rel_ty (update_ty_rel_env xi X R) (Q :: rho)
          (open_ty_rec (S (length rho)) (Ty_FVar X) T)
          (open_ty_rec (S (length rho)) (Ty_FVar X) T) x y <->
        rel_ty xi ((Q :: rho) ++ [R]) T T x y).
      { intros x y; apply IHT with (d := S (length rho)) (xi := xi)
          (X := X) (R := R) (rho := Q :: rho); simpl; auto. }
      apply (proj2 (Hbody w1 w2)); exact Hwr.
  - inversion Hlc; subst; reflexivity.
Qed.

Lemma rel_ty_rho_agree : forall K T, lc_ty_at K T ->
  forall xi rho rho',
    (forall i, i < K -> forall x y,
      nth i rho (fun _ _ => False) x y <-> nth i rho' (fun _ _ => False) x y) ->
    forall v1 v2, rel_ty xi rho T T v1 v2 <-> rel_ty xi rho' T T v1 v2.
Proof.
  intros K T Hlc; induction Hlc; intros xi rho rho' Hagree v1 v2; simpl.
  - apply Hagree; assumption.
  - reflexivity.
  - assert (HA : forall x y, rel_ty xi rho T1 T1 x y <-> rel_ty xi rho' T1 T1 x y).
    { intros; apply IHHlc1; exact Hagree. }
    assert (HB : forall x y, rel_ty xi rho T2 T2 x y <-> rel_ty xi rho' T2 T2 x y).
    { intros; apply IHHlc2; exact Hagree. }
    split.
    + intros [Hv1 [Hv2 Hfun]]; split; [exact Hv1|]; split; [exact Hv2|].
      intros a b Harg.
      apply (proj2 (exp_rel_equiv _ _ _ _ _ _ _ _ _ _ HA)) in Harg.
      destruct (Hfun a b Harg) as [x [y [Hx [Hy [Hvx [Hvy Hr]]]]]].
      exists x,y; repeat split; auto; apply (proj1 (HB x y)); exact Hr.
    + intros [Hv1 [Hv2 Hfun]]; split; [exact Hv1|]; split; [exact Hv2|].
      intros a b Harg.
      apply (proj1 (exp_rel_equiv _ _ _ _ _ _ _ _ _ _ HA)) in Harg.
      destruct (Hfun a b Harg) as [x [y [Hx [Hy [Hvx [Hvy Hr]]]]]].
      exists x,y; repeat split; auto; apply (proj2 (HB x y)); exact Hr.
  - split.
    + intros [Hv1 [Hv2 Hall]]; split; [exact Hv1|]; split; [exact Hv2|].
      intros U1 U2 Q HU1 HU2 HQ.
      destruct (Hall U1 U2 Q HU1 HU2 HQ) as [x [y [Hx [Hy [Hvx [Hvy Hr]]]]]].
      exists x,y; repeat split; auto.
      assert (Hpre : forall i, i < S k -> forall a b,
        nth i (Q::rho) (fun _ _ => False) a b <-> nth i (Q::rho') (fun _ _ => False) a b).
      { intros [|i] Hi a b; simpl; [tauto|apply Hagree; lia]. }
      apply (proj1 (IHHlc xi (Q::rho) (Q::rho') Hpre x y)); exact Hr.
    + intros [Hv1 [Hv2 Hall]]; split; [exact Hv1|]; split; [exact Hv2|].
      intros U1 U2 Q HU1 HU2 HQ.
      destruct (Hall U1 U2 Q HU1 HU2 HQ) as [x [y [Hx [Hy [Hvx [Hvy Hr]]]]]].
      exists x,y; repeat split; auto.
      assert (Hpre : forall i, i < S k -> forall a b,
        nth i (Q::rho) (fun _ _ => False) a b <-> nth i (Q::rho') (fun _ _ => False) a b).
      { intros [|i] Hi a b; simpl; [tauto|apply Hagree; lia]. }
      apply (proj2 (IHHlc xi (Q::rho) (Q::rho') Hpre x y)); exact Hr.
  - reflexivity.
Qed.


Lemma rel_ty_open_subst : forall T d xi rho U,
  length rho = d -> lc_ty_at (S d) T -> locally_closed_ty U ->
  forall v1 v2,
    rel_ty xi (rho ++ [rel_ty xi rho U U]) T T v1 v2 <->
    rel_ty xi rho (open_ty_rec d U T) (open_ty_rec d U T) v1 v2.
Proof.
  induction T; intros d xi rho U Hlen Hlc HU v1 v2; simpl in *.
  - inversion Hlc.
    destruct (Nat.eqb d n) eqn:E.
    + apply Nat.eqb_eq in E; subst n.
      rewrite app_nth2 by lia.
      subst i; rewrite Hlen, Nat.sub_diag; simpl; reflexivity.
    + assert (Hlt : n < length rho) by (apply Nat.eqb_neq in E; lia).
      rewrite app_nth1 by lia.
      destruct (Nat.eqb d n); [congruence|reflexivity].
  - reflexivity.
  - inversion Hlc; clear Hlc.
    assert (Hrel1 : forall x y,
      rel_ty xi (rho ++ [rel_ty xi rho U U]) T1 T1 x y <->
      rel_ty xi rho (open_ty_rec d U T1) (open_ty_rec d U T1) x y).
    { intros; apply IHT1; assumption. }
    assert (Hrel2 : forall x y,
      rel_ty xi (rho ++ [rel_ty xi rho U U]) T2 T2 x y <->
      rel_ty xi rho (open_ty_rec d U T2) (open_ty_rec d U T2) x y).
    { intros; apply IHT2; assumption. }
    split.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Ha.
      assert (Ha' : exp_rel xi (rho ++ [rel_ty xi rho U U]) T1 T1 a1 a2).
      { apply (proj2 (exp_rel_equiv _ _ _ _ _ _ _ _ _ _ Hrel1)); exact Ha. }
      destruct (Hfun a1 a2 Ha') as [b1 [b2 [Hb1 [Hb2 [Hbv1 [Hbv2 Hb]]]]]].
      exists b1,b2; repeat split; auto.
      apply (proj1 (Hrel2 b1 b2)); exact Hb.
    + intros [Hv1 [Hv2 Hfun]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros a1 a2 Ha.
      assert (Ha' : exp_rel xi rho (open_ty_rec d U T1) (open_ty_rec d U T1) a1 a2).
      { apply (proj1 (exp_rel_equiv _ _ _ _ _ _ _ _ _ _ Hrel1)); exact Ha. }
      destruct (Hfun a1 a2 Ha') as [b1 [b2 [Hb1 [Hb2 [Hbv1 [Hbv2 Hb]]]]]].
      exists b1,b2; repeat split; auto.
      apply (proj2 (Hrel2 b1 b2)); exact Hb.
  - inversion Hlc; clear Hlc.
    split.
    + intros [Hv1 [Hv2 Hall]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros A1 A2 Q HA1 HA2 HQ.
      specialize (Hall A1 A2 Q HA1 HA2 HQ) as [w1 [w2 [Hw1 [Hw2 [Hwv1 [Hwv2 Hw]]]]]].
      exists w1,w2; repeat split; auto.
      assert (Hopen : forall x y,
        rel_ty xi ((Q :: rho) ++ [rel_ty xi (Q :: rho) U U]) T T x y <->
        rel_ty xi (Q :: rho) (open_ty_rec (S d) U T) (open_ty_rec (S d) U T) x y).
      { intros; apply IHT; simpl; try lia; assumption. }
      assert (HUagree : forall x y, rel_ty xi rho U U x y <-> rel_ty xi (Q :: rho) U U x y).
      { intros; apply (rel_ty_rho_agree 0 U HU xi rho (Q :: rho)); intros; lia. }
      assert (Hctx : forall i, i < S (S d) -> forall x y,
        nth i (Q :: rho ++ [rel_ty xi rho U U]) (fun _ _ => False) x y <->
        nth i ((Q :: rho) ++ [rel_ty xi (Q :: rho) U U]) (fun _ _ => False) x y).
      { intros [|i] Hi x y; simpl; [tauto|].
        assert (Hid : i <= d) by lia.
        destruct (Nat.lt_ge_cases i d) as [Hlt|Hge].
        - rewrite !app_nth1 by lia; reflexivity.
        - assert (i = d) by lia; subst i.
          rewrite !app_nth2 by lia; rewrite Hlen, !Nat.sub_diag; simpl.
          apply HUagree. }
      pose proof (rel_ty_rho_agree (S (S d)) T H1 xi
        (Q :: rho ++ [rel_ty xi rho U U])
        ((Q :: rho) ++ [rel_ty xi (Q :: rho) U U]) Hctx w1 w2) as Htransport.
      apply (proj1 (Hopen w1 w2)).
      apply (proj1 Htransport); exact Hw.
    + intros [Hv1 [Hv2 Hall]]. split; [exact Hv1|]. split; [exact Hv2|].
      intros A1 A2 Q HA1 HA2 HQ.
      specialize (Hall A1 A2 Q HA1 HA2 HQ) as [w1 [w2 [Hw1 [Hw2 [Hwv1 [Hwv2 Hw]]]]]].
      exists w1,w2; repeat split; auto.
      assert (Hopen : forall x y,
        rel_ty xi ((Q :: rho) ++ [rel_ty xi (Q :: rho) U U]) T T x y <->
        rel_ty xi (Q :: rho) (open_ty_rec (S d) U T) (open_ty_rec (S d) U T) x y).
      { intros; apply IHT; simpl; try lia; assumption. }
      assert (HUagree : forall x y, rel_ty xi rho U U x y <-> rel_ty xi (Q :: rho) U U x y).
      { intros; apply (rel_ty_rho_agree 0 U HU xi rho (Q :: rho)); intros; lia. }
      assert (Hctx : forall i, i < S (S d) -> forall x y,
        nth i (Q :: rho ++ [rel_ty xi rho U U]) (fun _ _ => False) x y <->
        nth i ((Q :: rho) ++ [rel_ty xi (Q :: rho) U U]) (fun _ _ => False) x y).
      { intros [|i] Hi x y; simpl; [tauto|].
        assert (Hid : i <= d) by lia.
        destruct (Nat.lt_ge_cases i d) as [Hlt|Hge].
        - rewrite !app_nth1 by lia; reflexivity.
        - assert (i = d) by lia; subst i.
          rewrite !app_nth2 by lia; rewrite Hlen, !Nat.sub_diag; simpl.
          apply HUagree. }
      pose proof (rel_ty_rho_agree (S (S d)) T H1 xi
        (Q :: rho ++ [rel_ty xi rho U U])
        ((Q :: rho) ++ [rel_ty xi (Q :: rho) U U]) Hctx w1 w2) as Htransport.
      apply (proj2 Htransport).
      apply (proj2 (Hopen w1 w2)); exact Hw.
  - reflexivity.
Qed.

Lemma multi_trans : forall t u v, multi t u -> multi u v -> multi t v.
Proof. intros t u v H; induction H; intros Huv; eauto using multi. Qed.

Lemma multi_app_left : forall t t' u,
  multi t t' -> locally_closed_tm u ->
  multi (tm_app t u) (tm_app t' u).
Proof.
  intros t t' u H; induction H; intros Hu; eauto using multi, step.
Qed.

Lemma multi_app_right : forall v t t',
  value v -> multi t t' -> multi (tm_app v t) (tm_app v t').
Proof.
  intros v t t' Hv H; induction H; eauto using multi, step.
Qed.

Lemma multi_tapp : forall t t' T,
  multi t t' -> locally_closed_ty T ->
  multi (tm_tapp t T) (tm_tapp t' T).
Proof.
  intros t t' T H; induction H; intros HT; eauto using multi, step.
Qed.

Lemma multi_succ : forall t t', multi t t' -> multi (tm_succ t) (tm_succ t').
Proof.
  intros t t' H; induction H; eauto using multi, step.
Qed.

Lemma multi_rec_arg : forall n n' b s, multi n n' ->
  locally_closed_tm b -> locally_closed_tm s ->
  multi (tm_natrec n b s) (tm_natrec n' b s).
Proof. intros n n' b s H; induction H; intros Hb Hs; eauto using multi, step. Qed.

Lemma multi_rec_base : forall n b b' s, numeric_value n -> multi b b' ->
  locally_closed_tm s -> multi (tm_natrec n b s) (tm_natrec n b' s).
Proof. intros n b b' s Hn H; induction H; intros Hs; eauto using multi, step. Qed.

Lemma multi_rec_step : forall n b s s', numeric_value n -> value b -> multi s s' ->
  multi (tm_natrec n b s) (tm_natrec n b s').
Proof. intros n b s s' Hn Hb H; induction H; eauto using multi, step. Qed.

Lemma numeric_value_numeral : forall n, numeric_value (numeral n).
Proof. induction n; simpl; constructor; assumption. Qed.

Definition ty_subst_rel (xi : ty_rel_env) (rho : list term_rel)
    (T1 T2 : ty) : tm -> tm -> Prop := rel_ty xi rho T1 T2.

Definition term_env := atom -> tm.
Definition type_env := atom -> ty.

Fixpoint subst_env (sigma : term_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T b => tm_abs T (subst_env sigma b)
  | tm_app a b => tm_app (subst_env sigma a) (subst_env sigma b)
  | tm_tabs b => tm_tabs (subst_env sigma b)
  | tm_tapp a T => tm_tapp (subst_env sigma a) T
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (subst_env sigma a)
  | tm_natrec n b s => tm_natrec (subst_env sigma n) (subst_env sigma b) (subst_env sigma s)
  | tm_choice a b => tm_choice (subst_env sigma a) (subst_env sigma b)
  end.

Definition update_term_env (sigma : term_env) (x : atom) (v : tm) : term_env :=
  fun y => if Nat.eqb y x then v else sigma y.

Definition update_type_env (theta : type_env) (X : atom) (U : ty) : type_env :=
  fun Y => if Nat.eqb Y X then U else theta Y.

Fixpoint subst_ty_env (theta : type_env) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (subst_ty_env theta A) (subst_ty_env theta B)
  | Ty_All A => Ty_All (subst_ty_env theta A)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint subst_ty_env_tm (theta : type_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (subst_ty_env theta T) (subst_ty_env_tm theta b)
  | tm_app a b => tm_app (subst_ty_env_tm theta a) (subst_ty_env_tm theta b)
  | tm_tabs b => tm_tabs (subst_ty_env_tm theta b)
  | tm_tapp a T => tm_tapp (subst_ty_env_tm theta a) (subst_ty_env theta T)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (subst_ty_env_tm theta a)
  | tm_natrec n b s => tm_natrec (subst_ty_env_tm theta n)
      (subst_ty_env_tm theta b) (subst_ty_env_tm theta s)
  | tm_choice a b => tm_choice (subst_ty_env_tm theta a) (subst_ty_env_tm theta b)
  end.

Fixpoint ftv_tm_types (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_zero => []
  | tm_abs T b => ftv_ty T ++ ftv_tm_types b
  | tm_app a b | tm_choice a b => ftv_tm_types a ++ ftv_tm_types b
  | tm_tabs b | tm_succ b => ftv_tm_types b
  | tm_tapp a T => ftv_tm_types a ++ ftv_ty T
  | tm_natrec n b s => ftv_tm_types n ++ ftv_tm_types b ++ ftv_tm_types s
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_zero => []
  | tm_fvar x => [x]
  | tm_abs _ b | tm_tabs b | tm_succ b => fv_tm b
  | tm_app a b | tm_choice a b => fv_tm a ++ fv_tm b
  | tm_tapp a _ => fv_tm a
  | tm_natrec n b s => fv_tm n ++ fv_tm b ++ fv_tm s
  end.

Fixpoint ftv_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: G => ftv_ty T ++ ftv_context G
  end.

Lemma lookup_ftv_context : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (ftv_ty T) -> In X (ftv_context Gamma).
Proof.
  induction Gamma as [|[y A] G IH]; intros x T X Hlook Hin; simpl in *; try discriminate.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst; apply in_or_app; left; exact Hin.
  - apply in_or_app; right; eapply IH; eauto.
Qed.

Lemma rel_ty_value : forall T, forall xi rho,
  (forall X x y, xi X x y -> value x /\ value y) ->
  (forall R, In R rho -> forall x y, R x y -> value x /\ value y) ->
  forall x y, rel_ty xi rho T T x y -> value x /\ value y.
Proof.
  induction T; intros xi rho Hxi Hrho x y Hrel; simpl in Hrel.
  - destruct (Nat.lt_ge_cases n (length rho)) as [Hn|Hn].
    + eapply Hrho; [apply nth_In; exact Hn|exact Hrel].
    + rewrite nth_overflow in Hrel by exact Hn; contradiction.
  - eapply Hxi; exact Hrel.
  - destruct Hrel as [Hx [Hy _]]; split; assumption.
  - destruct Hrel as [Hx [Hy _]]; split; assumption.
  - destruct Hrel as [n [-> ->]]; split; apply v_nat; induction n; simpl; constructor; assumption.
Qed.

Lemma lc_ty_open_unchanged : forall K d U T,
  K <= d -> lc_ty_at K T -> open_ty_rec d U T = T.
Proof.
  intros K d U T Hkd Hlc.
  revert U d Hkd; dependent induction Hlc; intros U d Hkd; simpl.
  - destruct (Nat.eqb d i) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - f_equal; [apply IHHlc1|apply IHHlc2]; assumption.
  - f_equal; apply IHHlc; lia.
  - reflexivity.
Qed.

Lemma subst_ty_env_open_rec : forall theta X U d T,
  locally_closed_ty U ->
  (forall Y, locally_closed_ty (theta Y)) ->
  ~ In X (ftv_ty T) ->
  subst_ty_env (update_type_env theta X U) (open_ty_rec d (Ty_FVar X) T) =
  open_ty_rec d U (subst_ty_env theta T).
Proof.
  intros theta X U d T HU Htheta; revert d; induction T; intros d Hfresh; simpl in *.
  - destruct (Nat.eqb d n) eqn:E; simpl.
    + unfold update_type_env; simpl; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - unfold update_type_env; simpl.
    destruct (Nat.eqb a X) eqn:E.
    + apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; simpl; auto.
    + rewrite (lc_ty_open_unchanged 0 d U (theta a) (Nat.le_0_l _) (Htheta a)); reflexivity.
  - rewrite IHT1, IHT2; eauto using in_or_app.
  - simpl; rewrite IHT; eauto.
  - reflexivity.
Qed.

Lemma subst_ty_env_open_tm_rec : forall theta X U d t,
  locally_closed_ty U ->
  (forall Y, locally_closed_ty (theta Y)) ->
  ~ In X (ftv_tm_types t) ->
  subst_ty_env_tm (update_type_env theta X U) (open_tm_ty_rec d (Ty_FVar X) t) =
  open_tm_ty_rec d U (subst_ty_env_tm theta t).
Proof.
  intros theta X U d t HU Htheta; revert d; induction t; intros d Hfresh; simpl in *.
  - reflexivity.
  - reflexivity.
  - assert (Hft : ~ In X (ftv_ty t)) by
      (intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin).
    rewrite (subst_ty_env_open_rec theta X U d t HU Htheta Hft).
    rewrite IHt by (intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin).
    reflexivity.
  - rewrite IHt1, IHt2; auto using in_or_app.
  - rewrite IHt; auto.
  - rewrite IHt by (intro Hin; apply Hfresh; simpl; apply in_or_app; left; exact Hin).
    assert (Hft : ~ In X (ftv_ty t0)) by
      (intro Hin; apply Hfresh; simpl; apply in_or_app; right; exact Hin).
    rewrite (subst_ty_env_open_rec theta X U d t0 HU Htheta Hft).
    reflexivity.
  - reflexivity.
  - rewrite IHt; auto.
  - assert (H1 : ~ In X (ftv_tm_types t1)) by
      (apply (not_in_app_left X _ _ Hfresh)).
    assert (H2 : ~ In X (ftv_tm_types t2)) by
      (apply (not_in_app_left X (ftv_tm_types t2) (ftv_tm_types t3)
        (not_in_app_right X (ftv_tm_types t1)
          (ftv_tm_types t2 ++ ftv_tm_types t3) Hfresh))).
    assert (H3 : ~ In X (ftv_tm_types t3)) by
      (apply (not_in_app_right X (ftv_tm_types t2) (ftv_tm_types t3)
        (not_in_app_right X (ftv_tm_types t1)
          (ftv_tm_types t2 ++ ftv_tm_types t3) Hfresh))).
    rewrite (IHt1 d H1), (IHt2 d H2), (IHt3 d H3); reflexivity.
  - assert (H1 : ~ In X (ftv_tm_types t1)) by
      (apply (not_in_app_left X _ _ Hfresh)).
    assert (H2 : ~ In X (ftv_tm_types t2)) by
      (apply (not_in_app_right X _ _ Hfresh)).
    rewrite (IHt1 d H1), (IHt2 d H2); reflexivity.
Qed.

Lemma lc_tm_open_unchanged : forall K k d U t,
  k <= d -> lc_tm_at K k t -> open_tm_rec d U t = t.
Proof.
  intros K k d U t Hkd Hlc; revert d Hkd U; dependent induction Hlc;
    intros d Hkd U; simpl.
  - destruct (Nat.eqb d i) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - f_equal; apply IHHlc; lia.
  - f_equal; [apply IHHlc1|apply IHHlc2]; assumption.
  - f_equal; apply IHHlc; assumption.
  - f_equal; apply IHHlc; assumption.
  - reflexivity.
  - f_equal; apply IHHlc; assumption.
  - f_equal; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; assumption.
  - f_equal; [apply IHHlc1|apply IHHlc2]; assumption.
Qed.

Lemma lc_tm_ty_open_unchanged : forall K k d U t,
  K <= d -> lc_tm_at K k t -> open_tm_ty_rec d U t = t.
Proof.
  intros K k d U t Hkd Hlc; revert d Hkd U; dependent induction Hlc;
    intros d Hkd U; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (lc_ty_open_unchanged K d U T Hkd H); f_equal; apply IHHlc; assumption.
  - f_equal; [apply IHHlc1|apply IHHlc2]; assumption.
  - f_equal; apply IHHlc; lia.
  - f_equal.
    + apply IHHlc; assumption.
    + apply (lc_ty_open_unchanged K d U T Hkd H).
  - reflexivity.
  - f_equal; apply IHHlc; assumption.
  - f_equal; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; assumption.
  - f_equal; [apply IHHlc1|apply IHHlc2]; assumption.
Qed.

Lemma subst_env_open_tm_ty_rec : forall sigma d U t,
  (forall x, locally_closed_tm (sigma x)) ->
  subst_env sigma (open_tm_ty_rec d U t) =
  open_tm_ty_rec d U (subst_env sigma t).
Proof.
  intros sigma d U t Hsigma; revert d; induction t; intros d; simpl;
    try reflexivity; try (f_equal; eauto).
  - rewrite (lc_tm_ty_open_unchanged 0 0 d U (sigma a) (Nat.le_0_l _) (Hsigma a)); reflexivity.
Qed.


Lemma subst_env_open_rec : forall sigma x v k t,
  (forall y, locally_closed_tm (sigma y)) ->
  ~ In x (fv_tm t) ->
  subst_env (update_term_env sigma x v) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (subst_env sigma t).
Proof.
  intros sigma x v k t Hsigma; revert k; induction t; intros k Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + unfold update_term_env; simpl; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; simpl; auto.
    + unfold update_term_env; rewrite Nat.eqb_sym, E.
      rewrite (lc_tm_open_unchanged 0 0 k v (sigma a)
        (Nat.le_0_l _) (Hsigma a)).
      reflexivity.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto using in_or_app.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - reflexivity.
  - rewrite IHt; auto.
  - assert (H1 : ~ In x (fv_tm t1)) by
      (apply (not_in_app_left x _ _ Hfresh)).
    assert (H2 : ~ In x (fv_tm t2)) by
      (apply (not_in_app_left x (fv_tm t2) (fv_tm t3)
        (not_in_app_right x (fv_tm t1) (fv_tm t2 ++ fv_tm t3) Hfresh))).
    assert (H3 : ~ In x (fv_tm t3)) by
      (apply (not_in_app_right x (fv_tm t2) (fv_tm t3)
        (not_in_app_right x (fv_tm t1) (fv_tm t2 ++ fv_tm t3) Hfresh))).
    rewrite (IHt1 k H1), (IHt2 k H2), (IHt3 k H3); reflexivity.
  - rewrite IHt1, IHt2; auto using in_or_app.
Qed.

Definition ty_env_lc (Delta : ty_context) (theta : type_env) : Prop :=
  forall X, In X Delta -> locally_closed_ty (theta X).

Definition env_rel (xi : ty_rel_env) (Gamma : context)
    (sigma1 sigma2 : term_env) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    exp_rel xi [] T T (sigma1 x) (sigma2 x).

Definition rel_tctx (xi : ty_rel_env) (rho : list term_rel)
    (Gamma : context) (sigma1 sigma2 : term_env) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    exp_rel xi rho T T (sigma1 x) (sigma2 x).

Definition rel_tyctx (Delta1 Delta2 : ty_context) (xi : ty_rel_env) : Prop :=
  forall X, In X Delta1 -> In X Delta2 -> exists U1 U2,
    wf_ty Delta1 U1 /\ wf_ty Delta2 U2 /\
    forall v1 v2, xi X v1 v2 -> rel_ty xi [] U1 U2 v1 v2.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H; unfold locally_closed_tm in *.
  - constructor.
  - constructor; exact IHnumeric_value.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; subst; eauto using numeric_value_lc. Qed.

Lemma lc_ty_open_inv : forall K d U T,
  lc_ty_at (K + d) (open_ty_rec d U T) ->
  lc_ty_at (S (K + d)) T.
Proof.
  intros K d U T; revert K d U; induction T; intros K d U H; simpl in H.
  - destruct (Nat.eqb d n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - inversion H; constructor.
  - inversion H; subst; constructor; [eapply IHT1|eapply IHT2]; eauto.
  - inversion H; subst.
    replace (S (K + d)) with (K + S d) in H2 by lia.
    constructor.
    replace (S (S (K + d))) with (S (K + S d)) by lia.
    exact (IHT K (S d) U H2).
  - constructor.
Qed.

Lemma lc_ty_open_same : forall K d U T,
  0 < K ->
  lc_ty_at (K + d) (open_ty_rec d U T) ->
  lc_ty_at (K + d) T.
Proof.
  intros K d U T; revert K d U; induction T; intros K d U HK H; simpl in H.
  - destruct (Nat.eqb d n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - inversion H; constructor.
  - inversion H; subst; constructor; [eapply IHT1|eapply IHT2]; eauto.
  - inversion H; subst.
    replace (S (K + d)) with (K + S d) in H2 by lia.
    constructor.
    replace (S (K + d)) with (K + S d) by lia.
    exact (IHT K (S d) U HK H2).
  - constructor.
Qed.

Lemma lc_tm_open_inv : forall K k u t,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k u t; revert K k u; induction t; intros K k u H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - inversion H; constructor.
  - inversion H; subst; constructor.
    + assumption.
    + eapply IHt; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor. eapply IHt; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inv : forall K d k U t,
  lc_tm_at (K + d) k (open_tm_ty_rec d U t) ->
  lc_tm_at (S (K + d)) k t.
Proof.
  intros K d k U t; revert K d k U; induction t; intros K d k U H; simpl in H.
  - inversion H; subst; constructor; lia.
  - inversion H; constructor.
  - inversion H; subst; constructor.
    + eapply lc_ty_open_inv; eauto.
    + eapply IHt; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst.
    replace (S (K + d)) with (K + S d) in H3 by lia.
    constructor.
    replace (S (S (K + d))) with (S (K + S d)) by lia.
    exact (IHt K (S d) k U H3).
  - inversion H; subst; constructor.
    + eapply IHt; eauto.
    + eapply lc_ty_open_inv; eauto.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_same : forall K d k U t,
  0 < K ->
  lc_tm_at (K + d) k (open_tm_ty_rec d U t) ->
  lc_tm_at (K + d) k t.
Proof.
  intros K d k U t; revert K d k U; induction t; intros K d k U HK H; simpl in H.
  - inversion H; subst; constructor; assumption.
  - inversion H; constructor.
  - inversion H; subst; constructor.
    + eapply lc_ty_open_same; eauto.
    + eapply IHt; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst.
    replace (S (K + d)) with (K + S d) in H3 by lia.
    constructor.
    replace (S (K + d)) with (K + S d) by lia.
    exact (IHt K (S d) k U HK H3).
  - inversion H; subst; constructor.
    + eapply IHt; eauto.
    + eapply lc_ty_open_same; eauto.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Fixpoint list_max (xs : list nat) : nat :=
  match xs with [] => 0 | x :: rest => Nat.max x (list_max rest) end.

Lemma in_list_max : forall x xs, In x xs -> x <= list_max xs.
Proof.
  intros x xs; induction xs as [|a xs IH]; simpl; intros H; [contradiction|].
  destruct H as [->|H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma exists_fresh_atom : forall xs : list atom, exists x, ~ In x xs.
Proof.
  intros xs; exists (S (list_max xs)); intro H.
  pose proof (in_list_max _ _ H); lia.
Qed.

Lemma lc_ty_weaken : forall K T, lc_ty_at K T ->
  forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros K T H; induction H; intros K' Hle.
  - constructor; lia.
  - constructor.
  - constructor; [apply IHlc_ty_at1|apply IHlc_ty_at2]; lia.
  - constructor; apply IHlc_ty_at; lia.
  - constructor.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at (length Delta) T.
Proof.
  intros Delta T H; induction H.
  - constructor.
  - constructor; assumption.
  - destruct (exists_fresh_atom L) as [X HX].
    pose proof (H0 X HX) as Hopen.
    unfold open_ty in Hopen.
    simpl in Hopen.
    replace (S (length Delta)) with (S (length Delta) + 0) in Hopen by lia.
    apply lc_ty_all.
    pose proof (lc_ty_open_same (S (length Delta)) 0 (Ty_FVar X) T
      ltac:(lia) Hopen) as Hsame.
    replace (S (length Delta) + 0) with (S (length Delta)) in Hsame by lia.
    exact Hsame.
  - constructor.
Qed.

Lemma wf_ty_mono : forall Delta Delta' T,
  (forall X, In X Delta -> In X Delta') -> wf_ty Delta T -> wf_ty Delta' T.
Proof.
  intros Delta Delta' T Hinc Hwf; revert Delta' Hinc; induction Hwf;
    intros Delta' Hinc.
  - constructor; apply Hinc; assumption.
  - constructor; [apply IHHwf1|apply IHHwf2]; assumption.
  - apply WF_All with (L := L); intros X HX.
    refine (H0 X HX (X :: Delta') _).
    intros Y HY; simpl in HY; destruct HY as [->|HY].
    + simpl; auto.
    + simpl; right; apply Hinc; exact HY.
  - constructor.
Qed.

Lemma wf_ty_lc0 : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hwf; induction Hwf.
  - constructor.
  - constructor; assumption.
  - destruct (exists_fresh_atom L) as [X HX].
    pose proof (H0 X HX) as Hopen.
    unfold open_ty in Hopen.
    apply lc_ty_all.
    exact (lc_ty_open_inv 0 0 (Ty_FVar X) T Hopen).
  - constructor.
Qed.

Lemma ty_subst_open_commute : forall T X U Z d,
  X <> Z -> locally_closed_ty U ->
  ty_subst X U (open_ty_rec d (Ty_FVar Z) T) =
  open_ty_rec d (Ty_FVar Z) (ty_subst X U T).
Proof.
  induction T; intros X U Z d HX HU; simpl.
  - destruct (Nat.eqb d n); simpl.
    + destruct (Nat.eqb X Z) eqn:E; [apply Nat.eqb_eq in E; contradiction|reflexivity].
    + reflexivity.
  - destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E; subst a.
      rewrite (lc_ty_open_unchanged 0 d (Ty_FVar Z) U (Nat.le_0_l _) HU).
      reflexivity.
    + destruct (Nat.eqb d a); simpl.
      * destruct (Nat.eqb X Z); [congruence|reflexivity].
      * reflexivity.
  - f_equal; [apply IHT1|apply IHT2]; assumption.
  - f_equal; apply IHT; assumption.
  - reflexivity.
Qed.

Lemma ty_subst_open_fresh_rec : forall T X U d,
  ~ In X (ftv_ty T) -> locally_closed_ty U ->
  ty_subst X U (open_ty_rec d (Ty_FVar X) T) = open_ty_rec d U T.
Proof.
  induction T; intros X U d Hfresh HU; simpl in *.
  - destruct (Nat.eqb d n); simpl.
    + destruct (Nat.eqb X X) eqn:E; [reflexivity|apply Nat.eqb_neq in E; contradiction].
    + reflexivity.
  - destruct (Nat.eqb a X) eqn:E.
    + apply Nat.eqb_eq in E; subst; exfalso; apply Hfresh; simpl; auto.
    + rewrite Nat.eqb_sym, E; reflexivity.
  - assert (H1 : ~ In X (ftv_ty T1)) by (apply not_in_app_left with (ys := ftv_ty T2); exact Hfresh).
    assert (H2 : ~ In X (ftv_ty T2)) by (apply not_in_app_right with (xs := ftv_ty T1); exact Hfresh).
    rewrite (IHT1 X U d H1 HU), (IHT2 X U d H2 HU); reflexivity.
  - rewrite IHT; eauto.
  - reflexivity.
Qed.

Lemma ty_subst_open_fresh : forall T X U,
  ~ In X (ftv_ty T) -> locally_closed_ty U ->
  ty_subst X U (open_ty T (Ty_FVar X)) = open_ty T U.
Proof. intros; unfold open_ty; apply ty_subst_open_fresh_rec; assumption. Qed.

Lemma wf_ty_subst_general : forall Delta T, wf_ty Delta T ->
  forall Delta' X U,
    wf_ty Delta' U ->
    (forall Y, In Y Delta -> Y <> X -> In Y Delta') ->
    wf_ty Delta' (ty_subst X U T).
Proof.
  intros Delta T Hwf; induction Hwf; intros Delta' Xs U HU Hinc; simpl.
  - destruct (Nat.eqb Xs X) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact HU.
    + constructor; apply Hinc; [assumption|intro Heq; subst; rewrite Nat.eqb_refl in E; discriminate].
  - constructor; [apply IHHwf1|apply IHHwf2]; assumption.
  - apply WF_All with (L := Xs :: L).
    intros Z HZ.
    assert (HZL : ~ In Z L) by (intro Hin; apply HZ; simpl; auto).
    assert (HZX : Z <> Xs) by (intro Heq; subst; apply HZ; simpl; auto).
    assert (HU' : wf_ty (Z :: Delta') U).
    { eapply wf_ty_mono; [|exact HU]. intros Y HY; simpl; auto. }
    assert (Hinc' : forall Y, In Y (Z :: Delta) -> Y <> Xs -> In Y (Z :: Delta')).
    { intros Y HY Hneq; simpl in HY; destruct HY as [->|HY].
      - simpl; auto.
      - simpl; right; apply Hinc; assumption. }
    specialize (H0 Z HZL (Z :: Delta') Xs U HU' Hinc') as Hsub.
    unfold open_ty.
    rewrite <- (ty_subst_open_commute T Xs U Z 0 (not_eq_sym HZX) (wf_ty_lc0 _ _ HU')).
    exact Hsub.
  - constructor.
Qed.

Lemma wf_ty_open : forall Delta T U,
  wf_ty Delta (Ty_All T) -> wf_ty Delta U ->
  wf_ty Delta (open_ty T U).
Proof.
  intros Delta T U HAll HU.
  inversion HAll as [| |L D T0 Hbody|]; subst.
  destruct (exists_fresh_atom (L ++ ftv_ty T)) as [X HX].
  assert (HXL : ~ In X L) by (intro Hin; apply HX; repeat rewrite in_app_iff; simpl; tauto).
  assert (HfreshT : ~ In X (ftv_ty T)) by (intro Hin; apply HX; repeat rewrite in_app_iff; simpl; tauto).
  assert (HD : wf_ty (X :: Delta) U).
  { eapply wf_ty_mono; [|exact HU]. intros Y HY; simpl; auto. }
  pose proof (wf_ty_subst_general (X :: Delta) (open_ty T (Ty_FVar X))
    (Hbody X HXL) Delta X U HU
    (fun Y HY Hneq =>
       match HY with
       | or_introl Heq => False_rect _ (Hneq (eq_sym Heq))
       | or_intror Hin => Hin
       end)) as Hsub.
  rewrite (ty_subst_open_fresh T X U HfreshT (wf_ty_lc0 _ _ HU)) in Hsub.
  exact Hsub.
Qed.

Lemma has_type_wf : forall Delta Gamma t T, has_type Delta Gamma t T -> wf_ty Delta T.
Proof.
  intros Delta Gamma t T HT; induction HT.
  - exact H0.
  - constructor; [exact H|].
    destruct (exists_fresh_atom L) as [x Hx].
    exact (H1 x Hx).
  - inversion IHHT1; assumption.
  - apply WF_All with (L := L); intros X HX; exact (H0 X HX).
  - eapply wf_ty_open; eauto.
  - constructor.
  - constructor; exact IHHT.
  - exact IHHT2.
  - exact IHHT2.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at (length Delta) 0 t.
Proof.
  intros Delta Gamma t T HT; induction HT.
  - constructor.
  - constructor.
    + eapply wf_ty_lc; eauto.
    + destruct (exists_fresh_atom L) as [x Hx].
      apply lc_tm_open_inv with (u := tm_fvar x).
      apply H1; exact Hx.
  - econstructor; eauto.
  - constructor.
    destruct (exists_fresh_atom L) as [X HX].
    pose proof (H0 X HX) as Hopen.
    unfold open_tm_ty in Hopen; simpl in Hopen.
    replace (length (X :: Delta)) with (S (length Delta)) in Hopen by reflexivity.
    replace (S (length Delta)) with (S (length Delta) + 0) in Hopen by lia.
    pose proof (lc_tm_ty_open_same (S (length Delta)) 0 0 (Ty_FVar X)
      t ltac:(lia) Hopen) as Hsame.
    replace (S (length Delta) + 0) with (S (length Delta)) in Hsame by lia.
    exact Hsame.
  - econstructor; eauto using wf_ty_lc.
  - constructor.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma has_type_lc0 : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T HT; induction HT.
  - constructor.
  - unfold locally_closed_tm.
    constructor.
    + exact (wf_ty_lc0 _ _ H).
    + destruct (exists_fresh_atom L) as [x Hx].
      apply lc_tm_open_inv with (u := tm_fvar x).
      apply H1; exact Hx.
  - unfold locally_closed_tm; econstructor; eauto.
  - unfold locally_closed_tm.
    constructor.
    destruct (exists_fresh_atom L) as [X HX].
    pose proof (H0 X HX) as Hlc.
    unfold locally_closed_tm in Hlc.
    unfold open_tm_ty in Hlc.
    exact (lc_tm_ty_open_inv 0 0 0 (Ty_FVar X) t Hlc).
  - unfold locally_closed_tm; econstructor.
    + exact IHHT.
    + exact (wf_ty_lc0 _ _ H).
  - constructor.
  - unfold locally_closed_tm; constructor; eauto.
  - unfold locally_closed_tm; econstructor; eauto.
  - unfold locally_closed_tm; econstructor; eauto.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k t H; induction H; intros K' k' HK Hk.
  - constructor; lia.
  - constructor.
  - constructor.
    + eapply lc_ty_weaken; eauto.
    + apply IHlc_tm_at; lia.
  - econstructor; [apply IHlc_tm_at1|apply IHlc_tm_at2]; lia.
  - constructor; apply IHlc_tm_at; lia.
  - econstructor.
    + apply IHlc_tm_at; lia.
    + eapply lc_ty_weaken; eauto.
  - constructor.
  - constructor; apply IHlc_tm_at; lia.
  - econstructor; [apply IHlc_tm_at1|apply IHlc_tm_at2|apply IHlc_tm_at3]; lia.
  - econstructor; [apply IHlc_tm_at1|apply IHlc_tm_at2]; lia.
Qed.

Lemma lc_ty_subst_env : forall K T, lc_ty_at K T -> forall theta,
  (forall X, locally_closed_ty (theta X)) -> lc_ty_at K (subst_ty_env theta T).
Proof.
  intros K T H; induction H; intros theta Htheta; simpl.
  - constructor; assumption.
  - eapply lc_ty_weaken; [apply Htheta|lia].
  - econstructor; [apply IHlc_ty_at1|apply IHlc_ty_at2]; eauto.
  - constructor; apply IHlc_ty_at; eauto.
  - constructor.
Qed.

Lemma lc_tm_type_subst_env : forall K k t, lc_tm_at K k t -> forall theta,
  (forall X, locally_closed_ty (theta X)) ->
  lc_tm_at K k (subst_ty_env_tm theta t).
Proof.
  intros K k t H; induction H; intros theta Htheta; simpl.
  - constructor; assumption.
  - constructor.
  - constructor.
    + eapply lc_ty_subst_env; eauto.
    + apply IHlc_tm_at; auto.
  - econstructor; [apply IHlc_tm_at1|apply IHlc_tm_at2]; auto.
  - constructor; apply IHlc_tm_at; auto.
  - econstructor.
    + apply IHlc_tm_at; auto.
    + eapply lc_ty_subst_env; eauto.
  - constructor.
  - constructor; apply IHlc_tm_at; auto.
  - econstructor; [apply IHlc_tm_at1|apply IHlc_tm_at2|apply IHlc_tm_at3]; auto.
  - econstructor; [apply IHlc_tm_at1|apply IHlc_tm_at2]; auto.
Qed.

Lemma lc_tm_term_subst_env : forall K k t, lc_tm_at K k t -> forall sigma,
  (forall x, locally_closed_tm (sigma x)) -> lc_tm_at K k (subst_env sigma t).
Proof.
  intros K k t H; induction H; intros sigma Hsigma; simpl.
  - constructor; assumption.
  - eapply lc_tm_weaken; [apply Hsigma|lia|lia].
  - constructor.
    + assumption.
    + apply IHlc_tm_at; exact Hsigma.
  - econstructor; [apply IHlc_tm_at1|apply IHlc_tm_at2]; exact Hsigma.
  - constructor; apply IHlc_tm_at; exact Hsigma.
  - econstructor; [apply IHlc_tm_at|assumption]; exact Hsigma.
  - constructor.
  - constructor; apply IHlc_tm_at; exact Hsigma.
  - econstructor; [apply IHlc_tm_at1|apply IHlc_tm_at2|apply IHlc_tm_at3]; exact Hsigma.
  - econstructor; [apply IHlc_tm_at1|apply IHlc_tm_at2]; exact Hsigma.
Qed.

Lemma typed_inst_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall theta sigma,
    (forall X, locally_closed_ty (theta X)) ->
    (forall x, locally_closed_tm (sigma x)) ->
    locally_closed_tm (subst_env sigma (subst_ty_env_tm theta t)).
Proof.
  intros Delta Gamma t T HT; pose proof (has_type_lc0 _ _ _ _ HT) as Hlc.
  intros theta sigma Htheta Hsigma.
  eapply lc_tm_term_subst_env; [|exact Hsigma].
  eapply lc_tm_type_subst_env; eauto.
Qed.

Lemma env_rel_term_update : forall xi Gamma sigma1 sigma2 x A a1 a2,
  env_rel xi Gamma sigma1 sigma2 ->
  exp_rel xi [] A A a1 a2 ->
  env_rel xi (update Gamma x A)
    (update_term_env sigma1 x a1) (update_term_env sigma2 x a2).
Proof.
  intros xi Gamma sigma1 sigma2 x A a1 a2 Henv Harg y T Hlook.
  unfold update, lookup_context in Hlook; simpl in Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlook; subst T.
    unfold update_term_env; rewrite E; exact Harg.
  - unfold update_term_env; rewrite E.
    eapply Henv; exact Hlook.
Qed.

Lemma env_rel_type_update : forall xi Gamma sigma1 sigma2 X R,
  ~ In X (ftv_context Gamma) ->
  env_rel xi Gamma sigma1 sigma2 ->
  env_rel (update_ty_rel_env xi X R) Gamma sigma1 sigma2.
Proof.
  intros xi Gamma sigma1 sigma2 X R Hfresh Henv y T Hlook.
  assert (HTfresh : ~ In X (ftv_ty T)).
  { intro Hin; apply Hfresh; eapply lookup_ftv_context; eauto. }
  apply (proj2 (exp_rel_equiv _ _ _ _ _ _ _ _ _ _
    (fun v1 v2 => rel_ty_update_irrelevant T T xi X R []
      (ltac:(intro Hin; apply HTfresh; apply in_app_iff in Hin; tauto)) v1 v2))).
  apply Henv; exact Hlook.
Qed.

Lemma rel_value_safe : forall xi,
  (forall X x y, xi X x y -> value x /\ value y) ->
  forall T x y, rel_ty xi [] T T x y -> value x /\ value y.
Proof.
  intros xi Hxi T x y H.
  eapply rel_ty_value; eauto.
  intros R HR; inversion HR.
Qed.

Lemma subst_ty_env_tm_open_tm_rec : forall theta t k x,
  subst_ty_env_tm theta (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (tm_fvar x) (subst_ty_env_tm theta t).
Proof.
  intros theta t; induction t; intros k x; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal; apply IHt; exact Hnone.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal; apply IHt.
  - f_equal; apply IHt.
  - reflexivity.
  - f_equal; apply IHt.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
  - f_equal; [apply IHt1|apply IHt2].
Qed.

Lemma subst_ty_env_tm_open_tm : forall theta t x,
  subst_ty_env_tm theta (open_tm t (tm_fvar x)) =
  open_tm (subst_ty_env_tm theta t) (tm_fvar x).
Proof. intros; unfold open_tm; apply subst_ty_env_tm_open_tm_rec. Qed.

Lemma fv_tm_ty_subst : forall theta t, fv_tm (subst_ty_env_tm theta t) = fv_tm t.
Proof.
  intros theta t; induction t; simpl; try reflexivity;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3; reflexivity.
Qed.

Lemma fv_tm_open_rec_incl : forall t k u x,
  In x (fv_tm t) -> In x (fv_tm (open_tm_rec k u t)).
Proof.
  induction t; intros k u x Hin; simpl in *.
  - contradiction.
  - exact Hin.
  - eapply IHt; eauto.
  - apply in_app_iff in Hin; apply in_app_iff.
    destruct Hin as [Hin|Hin]; [left; eapply IHt1|right; eapply IHt2]; eauto.
  - eapply IHt; eauto.
  - eapply IHt; eauto.
  - contradiction.
  - eapply IHt; eauto.
  - apply in_app_iff in Hin; destruct Hin as [HinAB|HinS].
    + apply in_app_iff; left; eapply IHt1; eauto.
    + apply in_app_iff in HinS; apply in_app_iff.
      destruct HinS as [HinB|HinC].
      * right; apply in_app_iff; left; eapply IHt2; eauto.
      * right; apply in_app_iff; right; eapply IHt3; eauto.
  - apply in_app_iff in Hin; apply in_app_iff.
    destruct Hin; [left; eapply IHt1|right; eapply IHt2]; eauto.
Qed.

Lemma fv_tm_open_ty_eq : forall t k U, fv_tm (open_tm_ty_rec k U t) = fv_tm t.
Proof.
  induction t; intros k U; simpl; try reflexivity;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2; try rewrite IHt3; reflexivity.
Qed.

Lemma lookup_update_neq : forall Gamma x A y B,
  x <> y -> lookup_context y (update Gamma x A) = Some B ->
  lookup_context y Gamma = Some B.
Proof.
  intros Gamma x A y B Hneq Hlook; unfold update, lookup_context in *; simpl in *.
  assert (E : Nat.eqb y x = false).
  { apply Nat.eqb_neq; intro Heq; apply Hneq; symmetry; exact Heq. }
  rewrite E in Hlook; exact Hlook.
Qed.

Lemma has_type_fv_context : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall x, In x (fv_tm t) -> exists A, lookup_context x Gamma = Some A.
Proof.
  intros Delta Gamma t T HT; induction HT; intros y Hy.
  - simpl in Hy; destruct Hy as [->|[]]; eexists; eauto.
  - simpl in Hy.
    destruct (exists_fresh_atom (L ++ [y])) as [z Hz].
    assert (HzL : ~ In z L) by (intro Hin; apply Hz; apply in_app_iff; left; exact Hin).
    assert (Hzy : z <> y).
    { intro Heq; subst; apply Hz; apply in_app_iff; right; simpl; auto. }
    assert (Hyopen : In y (fv_tm (open_tm t2 (tm_fvar z)))).
    { unfold open_tm; eapply fv_tm_open_rec_incl; exact Hy. }
    destruct (H1 z HzL y Hyopen) as [A HA].
    exists A; eapply lookup_update_neq; [exact Hzy|exact HA].
  - simpl in Hy; apply in_app_iff in Hy; destruct Hy as [Hy|Hy].
    + destruct (IHHT1 y Hy) as [A HA]; eexists; exact HA.
    + destruct (IHHT2 y Hy) as [A HA]; eexists; exact HA.
  - simpl in Hy.
    destruct (exists_fresh_atom L) as [X HX].
    eapply H0; eauto.
    unfold open_tm_ty; rewrite (fv_tm_open_ty_eq t 0 (Ty_FVar X)); exact Hy.
  - simpl in Hy; exact (IHHT y Hy).
  - contradiction.
  - simpl in Hy; destruct (IHHT y Hy) as [A HA]; eexists; exact HA.
  - simpl in Hy; apply in_app_iff in Hy; destruct Hy as [Hy|HyBS].
    + destruct (IHHT1 y Hy) as [A HA]; eexists; exact HA.
    + apply in_app_iff in HyBS; destruct HyBS as [Hy|Hy].
      * destruct (IHHT2 y Hy) as [A HA]; eexists; exact HA.
      * destruct (IHHT3 y Hy) as [A HA]; eexists; exact HA.
  - simpl in Hy; apply in_app_iff in Hy; destruct Hy as [Hy|Hy].
    + destruct (IHHT1 y Hy) as [A HA]; eexists; exact HA.
    + destruct (IHHT2 y Hy) as [A HA]; eexists; exact HA.
Qed.


Lemma relational_identity_path : forall xi t U v,
  exp_rel xi [] (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0)))
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) t t ->
  locally_closed_ty U -> value v ->
  tm_app (tm_tapp t U) v -->* v.
Proof.
  intros xi t U v Ht HU Hv.
  destruct Ht as [f1 [f2 [Hf1 [Hf2 [Hfv1 [Hfv2 Hrel]]]]]].
  simpl in Hrel.
  destruct Hrel as [Hfv1' [Hfv2' Hall]].
  set (R := fun x y : tm => x = v /\ y = v).
  assert (HR : forall x y, R x y -> value x /\ value y).
  { intros x y [-> ->]; auto. }
  specialize (Hall U U R HU HU HR).
  destruct Hall as [g1 [g2 [Hg1 [Hg2 [Hgv1 [Hgv2 Hgre]]]]]].
  simpl in Hgre.
  destruct Hgre as [Hgv1' [Hgv2' Hfun]].
  assert (Harg : exp_rel xi [R] (Ty_BVar 0) (Ty_BVar 0) v v).
  { exists v, v; split; [constructor|]; split; [constructor|];
    split; [exact Hv|]; split; [exact Hv|]; simpl; split; reflexivity. }
  specialize (Hfun v v Harg).
  destruct Hfun as [z1 [z2 [Hz1 [Hz2 [Hzv1 [Hzv2 Hzrel]]]]]].
  unfold R in Hzrel.
  destruct Hzrel as [Hz1v Hz2v].
  subst z1 z2.
  eapply multi_trans.
  - eapply multi_app_left with (u := v).
    + exact (multi_tapp t f1 U Hf1 HU).
    + apply value_lc; exact Hv.
  - eapply multi_trans.
    + exact (multi_app_left (tm_tapp f1 U) g1 v Hg1 (value_lc v Hv)).
    + exact Hz1.
Qed.

Lemma has_type_empty_fv : forall Delta t T,
  has_type Delta empty t T -> forall x, In x (fv_tm t) -> False.
Proof.
  intros Delta t T HT x Hin.
  destruct (has_type_fv_context Delta empty t T HT x Hin) as [A HA].
  discriminate.
Qed.

Lemma subst_ty_env_id : forall T, subst_ty_env (fun X => Ty_FVar X) T = T.
Proof. induction T; simpl; try rewrite IHT; try rewrite IHT1; try rewrite IHT2; reflexivity. Qed.

Lemma subst_ty_env_tm_id : forall t, subst_ty_env_tm (fun X => Ty_FVar X) t = t.
Proof.
  induction t; simpl; try rewrite subst_ty_env_id; try rewrite IHt;
    try rewrite IHt1; try rewrite IHt2; try rewrite IHt3; reflexivity.
Qed.

Lemma subst_env_const_empty : forall t,
  (forall x, In x (fv_tm t) -> False) ->
  subst_env (fun _ => tm_zero) t = t.
Proof.
  induction t; intros Hnone; simpl.
  - reflexivity.
  - exfalso; apply (Hnone a); simpl; auto.
  - f_equal; apply IHt; exact Hnone.
  - f_equal.
    + apply IHt1; intros x Hin; apply (Hnone x); apply in_app_iff; left; exact Hin.
    + apply IHt2; intros x Hin; apply (Hnone x); apply in_app_iff; right; exact Hin.
  - f_equal; apply IHt; exact Hnone.
  - f_equal; eapply IHt; exact Hnone.
  - reflexivity.
  - f_equal; apply IHt; exact Hnone.
  - f_equal.
    + apply IHt1; intros x Hin; apply (Hnone x); apply in_app_iff; left; exact Hin.
    + apply IHt2; intros x Hin; apply (Hnone x); apply in_app_iff; right.
      apply in_app_iff; left; exact Hin.
    + apply IHt3; intros x Hin; apply (Hnone x); apply in_app_iff; right.
      apply in_app_iff; right; exact Hin.
  - f_equal.
    + apply IHt1; intros x Hin; apply (Hnone x); apply in_app_iff; left; exact Hin.
    + apply IHt2; intros x Hin; apply (Hnone x); apply in_app_iff; right; exact Hin.
Qed.

Lemma fundamental : forall Delta Gamma t T, has_type Delta Gamma t T ->
  forall theta1 theta2 xi sigma1 sigma2,
    (forall X, locally_closed_ty (theta1 X)) ->
    (forall X, locally_closed_ty (theta2 X)) ->
    (forall x, locally_closed_tm (sigma1 x)) ->
    (forall x, locally_closed_tm (sigma2 x)) ->
    (forall X x y, xi X x y -> value x /\ value y) ->
    env_rel xi Gamma sigma1 sigma2 ->
    exp_rel xi [] T T
      (subst_env sigma1 (subst_ty_env_tm theta1 t))
      (subst_env sigma2 (subst_ty_env_tm theta2 t)).
Proof.
  intros Delta Gamma t T HT; induction HT;
    intros theta1 theta2 xi sigma1 sigma2 Htheta1 Htheta2 Hsigma1 Hsigma2 Hxi Henv.
  - exact (Henv x T H).
  - set (b1 := subst_env sigma1 (subst_ty_env_tm theta1 t2)).
    set (b2 := subst_env sigma2 (subst_ty_env_tm theta2 t2)).
    assert (Hlc1 : locally_closed_tm (tm_abs (subst_ty_env theta1 T1) b1)).
    { pose proof (typed_inst_lc Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)
        (@T_Abs L Delta Gamma T1 t2 T2 H H0) theta1 sigma1 Htheta1 Hsigma1) as Hclosed.
      simpl in Hclosed; exact Hclosed. }
    assert (Hlc2 : locally_closed_tm (tm_abs (subst_ty_env theta2 T1) b2)).
    { pose proof (typed_inst_lc Delta Gamma (tm_abs T1 t2) (Ty_Arrow T1 T2)
        (@T_Abs L Delta Gamma T1 t2 T2 H H0) theta2 sigma2 Htheta2 Hsigma2) as Hclosed.
      simpl in Hclosed; exact Hclosed. }
    exists (tm_abs (subst_ty_env theta1 T1) b1), (tm_abs (subst_ty_env theta2 T1) b2).
    split; [apply multi_refl|]; split; [apply multi_refl|].
    split; [apply v_abs; exact Hlc1|]; split; [apply v_abs; exact Hlc2|].
    simpl; split; [apply v_abs; exact Hlc1|]; split; [apply v_abs; exact Hlc2|].
    intros a1 a2 Harg.
    destruct Harg as [a1' [a2' [Ha1 [Ha2 [Hva1 [Hva2 Harel]]]]]].
    destruct (exists_fresh_atom (L ++ fv_tm t2)) as [z Hz].
    assert (HzL : ~ In z L) by (intro Hin; apply Hz; apply in_app_iff; left; exact Hin).
    assert (Hzfv : ~ In z (fv_tm t2)) by (intro Hin; apply Hz; apply in_app_iff; right; exact Hin).
    assert (Hctx' : env_rel xi (update Gamma z T1)
      (update_term_env sigma1 z a1') (update_term_env sigma2 z a2')).
    { eapply env_rel_term_update; [exact Henv|].
      exists a1',a2'; split; [apply multi_refl|]; split; [apply multi_refl|].
      split; [exact Hva1|]; split; [exact Hva2|exact Harel]. }
    assert (Hs1' : forall y, locally_closed_tm (update_term_env sigma1 z a1' y)).
    { intros y; unfold update_term_env; destruct (Nat.eqb y z); [apply value_lc; exact Hva1|apply Hsigma1]. }
    assert (Hs2' : forall y, locally_closed_tm (update_term_env sigma2 z a2' y)).
    { intros y; unfold update_term_env; destruct (Nat.eqb y z); [apply value_lc; exact Hva2|apply Hsigma2]. }
    pose proof (H1 z HzL theta1 theta2 xi
      (update_term_env sigma1 z a1') (update_term_env sigma2 z a2')
      Htheta1 Htheta2 Hs1' Hs2' Hxi Hctx') as Hbody.
    assert (Hfresh1 : ~ In z (fv_tm (subst_ty_env_tm theta1 t2))).
    { rewrite fv_tm_ty_subst; exact Hzfv. }
    assert (Hfresh2 : ~ In z (fv_tm (subst_ty_env_tm theta2 t2))).
    { rewrite fv_tm_ty_subst; exact Hzfv. }
    unfold b1, b2 in Hbody.
    rewrite !subst_ty_env_tm_open_tm in Hbody.
    unfold open_tm in Hbody.
    rewrite (subst_env_open_rec sigma1 z a1' 0 (subst_ty_env_tm theta1 t2) Hsigma1 Hfresh1) in Hbody.
    rewrite (subst_env_open_rec sigma2 z a2' 0 (subst_ty_env_tm theta2 t2) Hsigma2 Hfresh2) in Hbody.
    destruct Hbody as [r1 [r2 [Hr1 [Hr2 [Hrv1 [Hrv2 Hrr]]]]]].
    exists r1,r2.
    split.
    + eapply multi_trans.
      * eapply multi_app_right; [constructor; exact Hlc1|exact Ha1].
      * eapply multi_trans.
        -- eapply multi_step.
           ++ apply ST_AppAbs; [exact Hlc1|exact Hva1].
           ++ constructor.
        -- exact Hr1.
    + split.
      * eapply multi_trans.
        -- eapply multi_app_right; [constructor; exact Hlc2|exact Ha2].
        -- eapply multi_trans.
           ++ eapply multi_step.
              ** apply ST_AppAbs; [exact Hlc2|exact Hva2].
              ** constructor.
           ++ exact Hr2.
      * repeat split; assumption.
  - pose proof (IHHT1 theta1 theta2 xi sigma1 sigma2 Htheta1 Htheta2 Hsigma1 Hsigma2 Hxi Henv) as Hfunexp.
    pose proof (IHHT2 theta1 theta2 xi sigma1 sigma2 Htheta1 Htheta2 Hsigma1 Hsigma2 Hxi Henv) as Hargexp.
    destruct Hfunexp as [f1 [f2 [Hf1 [Hf2 [Hfv1 [Hfv2 Hfrel]]]]]].
    simpl in Hfrel; destruct Hfrel as [Hfv1' [Hfv2' Hfun]].
    destruct (Hfun _ _ Hargexp) as [r1 [r2 [Hr1 [Hr2 [Hrv1 [Hrv2 Hrr]]]]]].
    set (argtm1 := subst_env sigma1 (subst_ty_env_tm theta1 t2)).
    set (argtm2 := subst_env sigma2 (subst_ty_env_tm theta2 t2)).
    assert (Hlc_a1 : locally_closed_tm argtm1).
    { unfold argtm1; eapply typed_inst_lc; eauto. }
    assert (Hlc_a2 : locally_closed_tm argtm2).
    { unfold argtm2; eapply typed_inst_lc; eauto. }
    exists r1,r2; split.
    + eapply multi_trans.
      * eapply multi_app_left; [exact Hf1|exact Hlc_a1].
      * exact Hr1.
    + split.
      * eapply multi_trans.
        -- eapply multi_app_left; [exact Hf2|exact Hlc_a2].
        -- exact Hr2.
      * repeat split; assumption.
  - assert (Hlc1 : locally_closed_tm
      (tm_tabs (subst_env sigma1 (subst_ty_env_tm theta1 t)))).
    { pose proof (typed_inst_lc Delta Gamma (tm_tabs t) (Ty_All T)
        (@T_TAbs L Delta Gamma t T H) theta1 sigma1 Htheta1 Hsigma1) as Hclosed.
      exact Hclosed. }
    assert (Hlc2 : locally_closed_tm
      (tm_tabs (subst_env sigma2 (subst_ty_env_tm theta2 t)))).
    { pose proof (typed_inst_lc Delta Gamma (tm_tabs t) (Ty_All T)
        (@T_TAbs L Delta Gamma t T H) theta2 sigma2 Htheta2 Hsigma2) as Hclosed.
      exact Hclosed. }
    exists (tm_tabs (subst_env sigma1 (subst_ty_env_tm theta1 t))),
           (tm_tabs (subst_env sigma2 (subst_ty_env_tm theta2 t))).
    split; [apply multi_refl|]; split; [apply multi_refl|].
    split; [apply v_tabs; exact Hlc1|]; split; [apply v_tabs; exact Hlc2|].
    simpl; split; [apply v_tabs; exact Hlc1|]; split; [apply v_tabs; exact Hlc2|].
    intros U1 U2 R HU1 HU2 HR.
    destruct (exists_fresh_atom
      (L ++ ftv_context Gamma ++ ftv_ty T ++ ftv_tm_types t)) as [X HX].
    assert (HXL : ~ In X L) by
      (intro Hin; apply HX; repeat rewrite in_app_iff; simpl; tauto).
    assert (HXG : ~ In X (ftv_context Gamma)) by
      (intro Hin; apply HX; repeat rewrite in_app_iff; simpl; tauto).
    assert (HXT : ~ In X (ftv_ty T)) by
      (intro Hin; apply HX; repeat rewrite in_app_iff; simpl; tauto).
    assert (HXt : ~ In X (ftv_tm_types t)) by
      (intro Hin; apply HX; repeat rewrite in_app_iff; simpl; tauto).
    set (th1 := update_type_env theta1 X U1).
    set (th2 := update_type_env theta2 X U2).
    set (xi' := update_ty_rel_env xi X R).
    assert (Hth1 : forall Y, locally_closed_ty (th1 Y)).
    { intros Y; unfold th1, update_type_env; destruct (Nat.eqb Y X) eqn:E.
      - apply Nat.eqb_eq in E; subst; exact HU1.
      - apply Htheta1. }
    assert (Hth2 : forall Y, locally_closed_ty (th2 Y)).
    { intros Y; unfold th2, update_type_env; destruct (Nat.eqb Y X) eqn:E.
      - apply Nat.eqb_eq in E; subst; exact HU2.
      - apply Htheta2. }
    assert (Hxi' : forall Y a b, xi' Y a b -> value a /\ value b).
    { intros Y a b Hrel; unfold xi', update_ty_rel_env in Hrel.
      destruct (Nat.eqb Y X); [eapply HR; exact Hrel|eapply Hxi; exact Hrel]. }
    assert (Henv' : env_rel xi' Gamma sigma1 sigma2).
    { unfold xi'; eapply env_rel_type_update; eauto. }
    pose proof (H0 X HXL th1 th2 xi' sigma1 sigma2 Hth1 Hth2
      Hsigma1 Hsigma2 Hxi' Henv') as Hb.
    unfold th1, th2, open_tm_ty in Hb.
    rewrite (subst_ty_env_open_tm_rec theta1 X U1 0 t HU1 Htheta1 HXt) in Hb.
    rewrite (subst_ty_env_open_tm_rec theta2 X U2 0 t HU2 Htheta2 HXt) in Hb.
    rewrite (subst_env_open_tm_ty_rec sigma1 0 U1 (subst_ty_env_tm theta1 t) Hsigma1) in Hb.
    rewrite (subst_env_open_tm_ty_rec sigma2 0 U2 (subst_ty_env_tm theta2 t) Hsigma2) in Hb.
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (wf_ty_lc0 Delta (Ty_All T)
        (has_type_wf Delta Gamma (tm_tabs t) (Ty_All T) (@T_TAbs L Delta Gamma t T H))) as Hall.
      inversion Hall; assumption. }
    assert (Hopenrel : forall a b,
      rel_ty xi' [] (open_ty T (Ty_FVar X)) (open_ty T (Ty_FVar X)) a b <->
      rel_ty xi [R] T T a b).
    { intros; apply rel_open_ty_rec with (d:=0) (X:=X) (R:=R);
        simpl; try lia; assumption. }
    apply (proj1 (exp_rel_equiv xi' xi [] [R]
      (open_ty T (Ty_FVar X)) (open_ty T (Ty_FVar X)) T T
      (open_tm_ty_rec 0 U1 (subst_env sigma1 (subst_ty_env_tm theta1 t)))
      (open_tm_ty_rec 0 U2 (subst_env sigma2 (subst_ty_env_tm theta2 t)))
      (fun a b => Hopenrel a b))) in Hb.
    destruct Hb as [r1 [r2 [Hr1 [Hr2 [Hrv1 [Hrv2 Hrel]]]]]].
    exists r1,r2; split.
    + eapply multi_trans.
      * eapply multi_step; [apply ST_TAppTabs; [exact Hlc1|exact HU1]|constructor].
      * exact Hr1.
    + split.
      * eapply multi_trans.
        -- eapply multi_step; [apply ST_TAppTabs; [exact Hlc2|exact HU2]|constructor].
        -- exact Hr2.
      * repeat split; assumption.
  - pose proof (IHHT theta1 theta2 xi sigma1 sigma2
      Htheta1 Htheta2 Hsigma1 Hsigma2 Hxi Henv) as HallExp.
    destruct HallExp as [f1 [f2 [Hf1 [Hf2 [Hfv1 [Hfv2 Hfrelation]]]]]].
    simpl in Hfrelation; destruct Hfrelation as [Hfv1' [Hfv2' Hall]].
    assert (HU1 : locally_closed_ty (subst_ty_env theta1 U)).
    { eapply lc_ty_subst_env; [exact (wf_ty_lc0 _ _ H)|exact Htheta1]. }
    assert (HU2 : locally_closed_ty (subst_ty_env theta2 U)).
    { eapply lc_ty_subst_env; [exact (wf_ty_lc0 _ _ H)|exact Htheta2]. }
    set (Q := rel_ty xi [] U U).
    assert (HQ : forall a b, Q a b -> value a /\ value b).
    { intros a b Hq; unfold Q in Hq; eapply rel_value_safe; eauto. }
    destruct (Hall (subst_ty_env theta1 U) (subst_ty_env theta2 U) Q
      HU1 HU2 HQ) as [r1 [r2 [Hr1 [Hr2 [Hrv1 [Hrv2 Hrel]]]]]].
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (wf_ty_lc0 Delta (Ty_All T) (has_type_wf Delta Gamma t (Ty_All T) HT)) as HAll.
      inversion HAll; assumption. }
    assert (HrelOpen : forall a b,
      rel_ty xi [Q] T T a b <->
      rel_ty xi [] (open_ty T U) (open_ty T U) a b).
    { intros a b; unfold Q; apply (rel_ty_open_subst T 0 xi [] U eq_refl HlcT (wf_ty_lc0 _ _ H) a b). }
    assert (Hbrel : rel_ty xi [] (open_ty T U) (open_ty T U) r1 r2).
    { apply (proj1 (HrelOpen r1 r2)); exact Hrel. }
    assert (Htyp1lc : locally_closed_ty (subst_ty_env theta1 U)).
    { exact HU1. }
    assert (Htyp2lc : locally_closed_ty (subst_ty_env theta2 U)).
    { exact HU2. }
    exists r1,r2; split.
    + eapply multi_trans.
      * eapply multi_tapp; [exact Hf1|exact Htyp1lc].
      * exact Hr1.
    + split.
      * eapply multi_trans.
        -- eapply multi_tapp; [exact Hf2|exact Htyp2lc].
        -- exact Hr2.
      * repeat split; assumption.
  - exists tm_zero,tm_zero; split; [apply multi_refl|]; split; [apply multi_refl|].
    split; [apply v_nat; constructor|]; split; [apply v_nat; constructor|].
    simpl; exists 0; split; reflexivity.
  - pose proof (IHHT theta1 theta2 xi sigma1 sigma2
      Htheta1 Htheta2 Hsigma1 Hsigma2 Hxi Henv) as Hn.
    destruct Hn as [n1 [n2 [Hn1 [Hn2 [Hnv1 [Hnv2 Hnr]]]]]].
    simpl in Hnr; destruct Hnr as [k [-> ->]].
    exists (tm_succ (numeral k)), (tm_succ (numeral k)).
    split; [apply multi_succ; exact Hn1|]; split; [apply multi_succ; exact Hn2|].
    split; [apply v_nat; constructor; apply numeric_value_numeral|].
    split; [apply v_nat; constructor; apply numeric_value_numeral|].
    simpl; exists (S k); split; reflexivity.
  - pose proof (IHHT1 theta1 theta2 xi sigma1 sigma2
      Htheta1 Htheta2 Hsigma1 Hsigma2 Hxi Henv) as Hnexp.
    pose proof (IHHT2 theta1 theta2 xi sigma1 sigma2
      Htheta1 Htheta2 Hsigma1 Hsigma2 Hxi Henv) as Hbexp.
    pose proof (IHHT3 theta1 theta2 xi sigma1 sigma2
      Htheta1 Htheta2 Hsigma1 Hsigma2 Hxi Henv) as Hsexp.
    destruct Hnexp as [nv1 [nv2 [Hnv1 [Hnv2 [Hnval1 [Hnval2 Hnrel]]]]]].
    simpl in Hnrel; destruct Hnrel as [k [Hnv1eq Hnv2eq]]; subst nv1 nv2.
    destruct Hbexp as [bv1 [bv2 [Hbv1 [Hbv2 [Hbval1 [Hbval2 Hbrel]]]]]].
    destruct Hsexp as [sv1 [sv2 [Hsv1 [Hsv2 [Hsval1 [Hsval2 Hsrel]]]]]].
    simpl in Hsrel; destruct Hsrel as [Hsval1' [Hsval2' Hstepfun]].
    assert (Hnum : numeric_value (numeral k)) by apply numeric_value_numeral.
    assert (Hreclc1 : locally_closed_tm
      (subst_env sigma1 (subst_ty_env_tm theta1 (tm_natrec n b s)))).
    { exact (typed_inst_lc Delta Gamma (tm_natrec n b s) T
        (@T_Rec Delta Gamma n b s T HT1 HT2 HT3) theta1 sigma1 Htheta1 Hsigma1). }
    assert (Hreclc2 : locally_closed_tm
      (subst_env sigma2 (subst_ty_env_tm theta2 (tm_natrec n b s)))).
    { exact (typed_inst_lc Delta Gamma (tm_natrec n b s) T
        (@T_Rec Delta Gamma n b s T HT1 HT2 HT3) theta2 sigma2 Htheta2 Hsigma2). }
    assert (Hb0lc1 : locally_closed_tm (subst_env sigma1 (subst_ty_env_tm theta1 b))).
    { exact (typed_inst_lc Delta Gamma b T HT2 theta1 sigma1 Htheta1 Hsigma1). }
    assert (Hb0lc2 : locally_closed_tm (subst_env sigma2 (subst_ty_env_tm theta2 b))).
    { exact (typed_inst_lc Delta Gamma b T HT2 theta2 sigma2 Htheta2 Hsigma2). }
    assert (Hs0lc1 : locally_closed_tm (subst_env sigma1 (subst_ty_env_tm theta1 s))).
    { exact (typed_inst_lc Delta Gamma s (Ty_Arrow Ty_Nat (Ty_Arrow T T))
        HT3 theta1 sigma1 Htheta1 Hsigma1). }
    assert (Hs0lc2 : locally_closed_tm (subst_env sigma2 (subst_ty_env_tm theta2 s))).
    { exact (typed_inst_lc Delta Gamma s (Ty_Arrow Ty_Nat (Ty_Arrow T T))
        HT3 theta2 sigma2 Htheta2 Hsigma2). }
    assert (HstepSafe : forall a1 a2, rel_ty xi [] Ty_Nat Ty_Nat a1 a2 -> value a1 /\ value a2).
    { intros; eapply rel_value_safe; eauto. }
    assert (Hnatarg : forall j,
      exp_rel xi [] Ty_Nat Ty_Nat (numeral j) (numeral j)).
    { intros j; exists (numeral j),(numeral j); split; [apply multi_refl|];
      split; [apply multi_refl|]; split; [apply v_nat; apply numeric_value_numeral|];
      split; [apply v_nat; apply numeric_value_numeral|].
      simpl; exists j; split; reflexivity. }
    assert (HbaseRel : rel_ty xi [] T T bv1 bv2) by exact Hbrel.
    assert (HstepRel : rel_ty xi [] (Ty_Arrow Ty_Nat (Ty_Arrow T T))
      (Ty_Arrow Ty_Nat (Ty_Arrow T T)) sv1 sv2).
    { simpl; split; [exact Hsval1'|]; split; [exact Hsval2'|exact Hstepfun]. }
    assert (Hiter : forall j,
      exp_rel xi [] T T
        (tm_natrec (numeral j) bv1 sv1)
        (tm_natrec (numeral j) bv2 sv2)).
    { induction j as [|j IH].
      - exists bv1,bv2; split.
        + eapply multi_step; [apply ST_RecZero; assumption|apply multi_refl].
        + split.
          * eapply multi_step; [apply ST_RecZero; assumption|apply multi_refl].
          * repeat split; assumption.
      - simpl in *.
        destruct (Hstepfun (numeral j) (numeral j) (Hnatarg j))
          as [p1 [p2 [Hp1 [Hp2 [Hpval1 [Hpval2 Hprel]]]]]].
        simpl in Hprel; destruct Hprel as [Hpval1' [Hpval2' Hinner]].
        destruct (Hinner (tm_natrec (numeral j) bv1 sv1)
          (tm_natrec (numeral j) bv2 sv2) IH)
          as [r1 [r2 [Hr1 [Hr2 [Hrval1 [Hrval2 Hrrel]]]]]].
        exists r1,r2; split.
        + eapply multi_trans.
          * eapply multi_step.
            -- apply ST_RecSucc; [apply numeric_value_numeral|exact Hbval1|exact Hsval1].
            -- apply multi_refl.
          * eapply multi_trans.
            -- eapply multi_app_left; [exact Hp1|].
               eapply lc_tm_rec; [apply numeric_value_lc; apply numeric_value_numeral|apply value_lc; exact Hbval1|apply value_lc; exact Hsval1].
            -- exact Hr1.
        + split.
          * eapply multi_trans.
            -- eapply multi_step.
               ++ apply ST_RecSucc; [apply numeric_value_numeral|exact Hbval2|exact Hsval2].
               ++ apply multi_refl.
            -- eapply multi_trans.
               ++ eapply multi_app_left; [exact Hp2|].
                  eapply lc_tm_rec; [apply numeric_value_lc; apply numeric_value_numeral|apply value_lc; exact Hbval2|apply value_lc; exact Hsval2].
               ++ exact Hr2.
          * repeat split; assumption. }
    destruct (Hiter k) as [r1 [r2 [Hri1 [Hri2 [Hrval1 [Hrval2 Hrrel]]]]]].
    pose proof (multi_rec_arg _ _ _ _ Hnv1 Hb0lc1 Hs0lc1) as Harg1.
    pose proof (multi_rec_arg _ _ _ _ Hnv2 Hb0lc2 Hs0lc2) as Harg2.
    pose proof (multi_rec_base (numeral k) (subst_env sigma1 (subst_ty_env_tm theta1 b)) bv1
      (subst_env sigma1 (subst_ty_env_tm theta1 s)) Hnum Hbv1 Hs0lc1) as Hbase1.
    pose proof (multi_rec_base (numeral k) (subst_env sigma2 (subst_ty_env_tm theta2 b)) bv2
      (subst_env sigma2 (subst_ty_env_tm theta2 s)) Hnum Hbv2 Hs0lc2) as Hbase2.
    pose proof (multi_rec_step (numeral k) bv1 (subst_env sigma1 (subst_ty_env_tm theta1 s)) sv1
      Hnum Hbval1 Hsv1) as Hstep1.
    pose proof (multi_rec_step (numeral k) bv2 (subst_env sigma2 (subst_ty_env_tm theta2 s)) sv2
      Hnum Hbval2 Hsv2) as Hstep2.
    exists r1,r2; split.
    + eapply multi_trans; [exact Harg1|].
      eapply multi_trans; [exact Hbase1|].
      eapply multi_trans; [exact Hstep1|exact Hri1].
    + split.
      * eapply multi_trans; [exact Harg2|].
        eapply multi_trans; [exact Hbase2|].
        eapply multi_trans; [exact Hstep2|exact Hri2].
      * repeat split; assumption.
  - pose proof (IHHT1 theta1 theta2 xi sigma1 sigma2
      Htheta1 Htheta2 Hsigma1 Hsigma2 Hxi Henv) as Hleft.
    assert (Hlc11 : locally_closed_tm (subst_env sigma1 (subst_ty_env_tm theta1 t1))).
    { exact (typed_inst_lc Delta Gamma t1 T HT1 theta1 sigma1 Htheta1 Hsigma1). }
    assert (Hlc12 : locally_closed_tm (subst_env sigma2 (subst_ty_env_tm theta2 t1))).
    { exact (typed_inst_lc Delta Gamma t1 T HT1 theta2 sigma2 Htheta2 Hsigma2). }
    assert (Hlc21 : locally_closed_tm (subst_env sigma1 (subst_ty_env_tm theta1 t2))).
    { exact (typed_inst_lc Delta Gamma t2 T HT2 theta1 sigma1 Htheta1 Hsigma1). }
    assert (Hlc22 : locally_closed_tm (subst_env sigma2 (subst_ty_env_tm theta2 t2))).
    { exact (typed_inst_lc Delta Gamma t2 T HT2 theta2 sigma2 Htheta2 Hsigma2). }
    destruct Hleft as [r1 [r2 [Hr1 [Hr2 [Hrv1 [Hrv2 Hrel]]]]]].
    exists r1,r2; split.
    + eapply multi_trans.
      * eapply multi_step; [apply ST_ChoiceLeft; assumption|apply multi_refl].
      * exact Hr1.
    + split.
      * eapply multi_trans.
        -- eapply multi_step; [apply ST_ChoiceLeft; assumption|apply multi_refl].
        -- exact Hr2.
      * repeat split; assumption.
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
  intros t Ht U v HU Hv Htv.
  assert (Hfv : forall x, In x (fv_tm t) -> False).
  { eapply has_type_empty_fv; exact Ht. }
  set (thetaid := fun X : atom => Ty_FVar X).
  set (sigma := fun _ : atom => tm_zero).
  set (xi := fun _ : atom => fun _ _ : tm => False).
  assert (Htheta : forall X, locally_closed_ty (thetaid X)).
  { intros; constructor. }
  assert (Hsigma : forall x, locally_closed_tm (sigma x)).
  { intros; constructor. }
  assert (Hxi : forall X x y, xi X x y -> value x /\ value y).
  { intros; contradiction. }
  assert (Henv : env_rel xi empty sigma sigma).
  { unfold env_rel, empty; intros x T Hlook; discriminate. }
  pose proof (fundamental [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
    thetaid thetaid xi sigma sigma Htheta Htheta Hsigma Hsigma Hxi Henv) as Hfund.
  rewrite subst_ty_env_tm_id in Hfund.
  unfold sigma in Hfund.
  rewrite (subst_env_const_empty t Hfv) in Hfund.
  eapply relational_identity_path; [exact Hfund| |exact Hv].
  exact (wf_ty_lc0 [] U HU).
Qed.

End SystemFParametricityNondeterminismRecursionHardTask.
