(** System F parametricity benchmark, Medium variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfRecursionMediumTask.

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
  | Ty_Bool : ty
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
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm
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

Notation "'Bool'" := Ty_Bool (in custom systemf_ty at level 0) : systemf_scope.
Notation "'true'" := tm_true (in custom systemf_tm at level 0) : systemf_scope.
Notation "'false'" := tm_false (in custom systemf_tm at level 0) : systemf_scope.
Notation "'if' t1 'then' t2 'else' t3" := (tm_if t1 t2 t3)
  (in custom systemf_tm at level 200, t1 custom systemf_tm, t2 custom systemf_tm, t3 custom systemf_tm at level 200) : systemf_scope.
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
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_rec k u t1) (open_tm_rec k u t2) (open_tm_rec k u t3)
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (open_tm_ty_rec k U t1) (open_tm_ty_rec k U t2) (open_tm_ty_rec k U t3)
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
  | Ty_Bool => Ty_Bool
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_ty_subst X U t1) (tm_ty_subst X U t2) (tm_ty_subst X U t3)
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
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (tm_subst x s t1) (tm_subst x s t2) (tm_subst x s t3)
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
  | lc_ty_bool : forall k, lc_ty_at k Ty_Bool
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
  | lc_tm_true : forall K k, lc_tm_at K k tm_true
  | lc_tm_false : forall K k, lc_tm_at K k tm_false
  | lc_tm_if : forall K k t1 t2 t3,
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 -> lc_tm_at K k (tm_if t1 t2 t3)
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
  | v_true : value tm_true
  | v_false : value tm_false
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
  | WF_Bool : forall Delta, wf_ty Delta Ty_Bool
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
  | T_True : forall Delta Gamma, has_type Delta Gamma tm_true Ty_Bool
  | T_False : forall Delta Gamma, has_type Delta Gamma tm_false Ty_Bool
  | T_If : forall Delta Gamma t1 t2 t3 T,
      has_type Delta Gamma t1 Ty_Bool ->
      has_type Delta Gamma t2 T -> has_type Delta Gamma t3 T ->
      has_type Delta Gamma (tm_if t1 t2 t3) T
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
  | EvalIfTrue : forall c t u v,
      evaluates c tm_true -> evaluates t v -> locally_closed_tm u ->
      evaluates (tm_if c t u) v
  | EvalIfFalse : forall c t u v,
      evaluates c tm_false -> locally_closed_tm t -> evaluates u v ->
      evaluates (tm_if c t u) v
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
  | Ty_Bool => (v1 = tm_true /\ v2 = tm_true) \/ (v1 = tm_false /\ v2 = tm_false)
  | Ty_Nat => v1 = v2 /\ numeric_value v1
  end.

Definition expression_relation eta rho T t1 t2 :=
  expression_lifting (value_relation eta rho T) t1 t2.

Lemma fresh_list : forall L : list atom,
  ~ In (S (fold_right Nat.max 0 L)) L.
Proof.
  induction L as [| head tail IH]; simpl.
  - tauto.
  - intros [Heq | Htail].
    + assert (head <= Nat.max head (fold_right Nat.max 0 tail)) by lia.
      lia.
    + assert (fold_right Nat.max 0 tail <=
              Nat.max head (fold_right Nat.max 0 tail)) by lia.
      assert (forall n, In n tail -> n <= fold_right Nat.max 0 tail).
      { clear -tail; induction tail as [| first rest IH']; simpl; intros n Hin.
        - contradiction.
        - destruct Hin as [<- | Hin]; [lia | specialize (IH' _ Hin); lia]. }
      specialize (H0 _ Htail); lia.
Qed.

Lemma lc_open_ty_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - constructor.
Qed.

Lemma lc_open_tm_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H;
    try (inversion H; subst; constructor; eauto; fail);
    try (constructor; fail).
  destruct (Nat.eqb k n) eqn:E.
  - apply Nat.eqb_eq in E; subst; constructor; lia.
  - inversion H; subst; constructor; lia.
Qed.

Lemma lc_open_tm_ty_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H;
    try (inversion H; subst; constructor; eauto using lc_open_ty_inv; fail);
    constructor.
Qed.

Lemma wf_ty_closed : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H; unfold locally_closed_ty in *;
    try (constructor; eauto; fail).
  set (X := S (fold_right Nat.max 0 L)).
  apply lc_ty_all; eapply lc_open_ty_inv.
  exact (H0 X (fresh_list L)).
Qed.

Lemma has_type_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H; unfold locally_closed_tm in *;
    try (solve [constructor; eauto using wf_ty_closed with core]).
  - apply lc_tm_abs.
    + eapply wf_ty_closed; eassumption.
    + set (x := S (fold_right Nat.max 0 L)).
      eapply lc_open_tm_inv.
      exact (H1 x (fresh_list L)).
  - apply lc_tm_tabs.
    set (X := S (fold_right Nat.max 0 L)).
    eapply lc_open_tm_ty_inv.
    exact (H0 X (fresh_list L)).
  - apply lc_tm_tapp; [assumption | eapply wf_ty_closed; eassumption].
Qed.

Lemma value_relation_values : forall T eta rho v1 v2,
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  induction T; intros eta rho v1 v2 H; simpl in H.
  - destruct (nth_error eta n) as [candidate |] eqn:E;
      [exact (candidate_values candidate _ _ H) | contradiction].
  - destruct (rho a) as [candidate |] eqn:E;
      [exact (candidate_values candidate _ _ H) | contradiction].
  - tauto.
  - tauto.
  - destruct H as [[-> ->] | [-> ->]]; auto with core.
  - destruct H as [-> H]; split; constructor; assumption.
Qed.

Definition relation_candidate (eta : list binary_candidate) (rho : binary_env)
    (T : ty) : binary_candidate :=
  {| candidate_relation := value_relation eta rho T;
     candidate_values := value_relation_values T eta rho |}.

Lemma numeric_value_closed : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H; unfold locally_closed_tm in *; eauto with core.
Qed.

Lemma value_closed : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; induction H; try assumption;
    try (unfold locally_closed_tm; auto with core).
  apply numeric_value_closed; assumption.
Qed.

Lemma related_application : forall eta rho A B f1 f2 arg1 arg2,
  expression_relation eta rho (Ty_Arrow A B) f1 f2 ->
  expression_relation eta rho A arg1 arg2 ->
  expression_relation eta rho B (tm_app f1 arg1) (tm_app f2 arg2).
Proof.
  intros eta rho A B f1 f2 arg1 arg2 Hf Harg.
  destruct Hf as [Hf1 [Hf2 [fun1 [fun2 [Heval1 [Heval2 Hfun]]]]]].
  destruct Harg as [Harg1 [Harg2 [val1 [val2 [Hval1 [Hval2 Hval]]]]]].
  simpl in Hfun.
  destruct Hfun as [_ [_ [type1 [body1 [type2 [body2
      [Hfun1 [Hfun2 Hbody]]]]]]]].
  subst fun1 fun2.
  specialize (Hbody val1 val2 Hval).
  destruct Hbody as [_ [_ [res1 [res2 [Hres1 [Hres2 Hres]]]]]].
  unfold expression_relation, expression_lifting, results_match.
  split; [unfold locally_closed_tm in *; constructor; assumption |].
  split; [unfold locally_closed_tm in *; constructor; assumption |].
  exists res1, res2; repeat split; try assumption.
  - eapply EvalApp; eauto.
  - eapply EvalApp; eauto.
Qed.

Lemma related_value : forall eta rho T v1 v2,
  value_relation eta rho T v1 v2 -> expression_relation eta rho T v1 v2.
Proof.
  intros eta rho T v1 v2 Hrel.
  pose proof (value_relation_values T eta rho v1 v2 Hrel) as [Hv1 Hv2].
  unfold expression_relation, expression_lifting, results_match.
  split; [apply value_closed; assumption |].
  split; [apply value_closed; assumption |].
  exists v1, v2; repeat split; eauto using EvalValue.
Qed.

Lemma related_if : forall eta rho T c1 c2 t1 t2 u1 u2,
  expression_relation eta rho Ty_Bool c1 c2 ->
  expression_relation eta rho T t1 t2 ->
  expression_relation eta rho T u1 u2 ->
  expression_relation eta rho T (tm_if c1 t1 u1) (tm_if c2 t2 u2).
Proof.
  intros eta rho T c1 c2 t1 t2 u1 u2 Hc Ht Hu.
  destruct Hc as [Hc1 [Hc2 [vc1 [vc2 [Hec1 [Hec2 Hvc]]]]]].
  destruct Ht as [Ht1 [Ht2 [vt1 [vt2 [Het1 [Het2 Hvt]]]]]].
  destruct Hu as [Hu1 [Hu2 [vu1 [vu2 [Heu1 [Heu2 Hvu]]]]]].
  unfold expression_relation, expression_lifting, results_match.
  split; [unfold locally_closed_tm in *; constructor; assumption |].
  split; [unfold locally_closed_tm in *; constructor; assumption |].
  simpl in Hvc.
  destruct Hvc as [[-> ->] | [-> ->]].
  - exists vt1, vt2; repeat split; eauto using EvalIfTrue.
  - exists vu1, vu2; repeat split; eauto using EvalIfFalse.
Qed.

Lemma related_succ : forall eta rho t1 t2,
  expression_relation eta rho Ty_Nat t1 t2 ->
  expression_relation eta rho Ty_Nat (tm_succ t1) (tm_succ t2).
Proof.
  intros eta rho t1 t2 [Hlc1 [Hlc2 [v1 [v2 [He1 [He2 Hrel]]]]]].
  destruct Hrel as [-> Hnumeric].
  unfold expression_relation, expression_lifting, results_match.
  split; [unfold locally_closed_tm in *; constructor; assumption |].
  split; [unfold locally_closed_tm in *; constructor; assumption |].
  exists (tm_succ v2), (tm_succ v2); repeat split;
    eauto using EvalSucc, nv_succ.
Qed.

Lemma related_rec_values : forall eta rho T k base1 base2 step1 step2,
  numeric_value k ->
  value_relation eta rho T base1 base2 ->
  value_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) step1 step2 ->
  expression_relation eta rho T
    (tm_natrec k base1 step1) (tm_natrec k base2 step2).
Proof.
  intros eta rho T k base1 base2 step1 step2 Hk.
  induction Hk as [| k Hk IH]; intros Hbase Hstep.
  - pose proof (value_relation_values T eta rho _ _ Hbase) as [Hbase1 Hbase2].
    pose proof (value_relation_values _ eta rho _ _ Hstep) as [Hstep1 Hstep2].
    unfold expression_relation, expression_lifting, results_match.
    split; [apply lc_tm_rec; [constructor | apply value_closed; assumption |
                             apply value_closed; assumption] |].
    split; [apply lc_tm_rec; [constructor | apply value_closed; assumption |
                             apply value_closed; assumption] |].
    exists base1, base2; repeat split; try assumption;
      (eapply EvalRecZero;
      [apply EvalValue; apply v_nat; apply nv_zero |
       apply EvalValue; assumption | apply EvalValue; assumption]).
  - pose proof (value_relation_values T eta rho _ _ Hbase) as [Hbase1 Hbase2].
    pose proof (value_relation_values _ eta rho _ _ Hstep) as [Hstep1 Hstep2].
    pose proof (IH Hbase Hstep) as Hrec.
    assert (Hnum : expression_relation eta rho Ty_Nat k k).
    { apply related_value; simpl; auto. }
    pose proof (related_application _ _ _ _ _ _ _ _
      (related_value _ _ _ _ _ Hstep) Hnum) as Hfirst.
    pose proof (related_application _ _ _ _ _ _ _ _ Hfirst Hrec) as Hsecond.
    destruct Hsecond as [_ [_ [res1 [res2 [Hres1 [Hres2 Hres]]]]]].
    unfold expression_relation, expression_lifting, results_match.
    split; [apply lc_tm_rec; [apply numeric_value_closed; constructor; assumption |
                             apply value_closed; assumption | apply value_closed; assumption] |].
    split; [apply lc_tm_rec; [apply numeric_value_closed; constructor; assumption |
                             apply value_closed; assumption | apply value_closed; assumption] |].
    exists res1, res2; repeat split; try assumption.
    + eapply EvalRecSucc with (k := k) (vb := base1) (vs := step1);
        eauto using EvalValue, nv_succ.
    + eapply EvalRecSucc with (k := k) (vb := base2) (vs := step2);
        eauto using EvalValue, nv_succ.
Qed.

Lemma numeric_evaluates_identity : forall n result,
  numeric_value n -> evaluates n result -> result = n.
Proof.
  intros n result Hnumeric; revert result.
  induction Hnumeric; intros result Heval; inversion Heval; subst;
    try reflexivity.
  f_equal; eapply IHHnumeric; eassumption.
Qed.

Lemma value_evaluates_identity : forall v result,
  value v -> evaluates v result -> result = v.
Proof.
  intros v result Hv Heval; inversion Hv; subst;
    inversion Heval; subst; eauto using numeric_evaluates_identity.
Qed.

Lemma rec_values_transfer : forall n b s k vb vs result,
  evaluates n k -> evaluates b vb -> evaluates s vs ->
  numeric_value k -> value vb -> value vs ->
  evaluates (tm_natrec k vb vs) result ->
  evaluates (tm_natrec n b s) result.
Proof.
  intros n b s k vb vs result Hn Hb Hs Hk Hvb Hvs Hrec.
  inversion Hrec; subst;
    try (match goal with H : value (tm_natrec _ _ _) |- _ =>
      inversion H; subst;
      match goal with N : numeric_value (tm_natrec _ _ _) |- _ => inversion N end
    end).
  - pose proof (numeric_evaluates_identity _ _ Hk H2) as Ezero.
    symmetry in Ezero; subst k.
    pose proof (value_evaluates_identity _ _ Hvb H4) as Ebase.
    subst result.
    pose proof (value_evaluates_identity _ _ Hvs H5) as Estep.
    subst vs0.
    eapply EvalRecZero; eassumption.
  - pose proof (numeric_evaluates_identity _ _ Hk H2) as Esucc.
    symmetry in Esucc; subst k.
    pose proof (value_evaluates_identity _ _ Hvb H4) as Ebase.
    subst vb0.
    pose proof (value_evaluates_identity _ _ Hvs H6) as Estep.
    subst vs0.
    eapply EvalRecSucc; eassumption.
Qed.

Lemma related_rec : forall eta rho T n1 n2 b1 b2 s1 s2,
  expression_relation eta rho Ty_Nat n1 n2 ->
  expression_relation eta rho T b1 b2 ->
  expression_relation eta rho (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s1 s2 ->
  expression_relation eta rho T
    (tm_natrec n1 b1 s1) (tm_natrec n2 b2 s2).
Proof.
  intros eta rho T n1 n2 b1 b2 s1 s2 Hn Hb Hs.
  destruct Hn as [Hn1 [Hn2 [k1 [k2 [Hen1 [Hen2 Hk]]]]]].
  destruct Hb as [Hb1 [Hb2 [vb1 [vb2 [Heb1 [Heb2 Hvb]]]]]].
  destruct Hs as [Hs1 [Hs2 [vs1 [vs2 [Hes1 [Hes2 Hvs]]]]]].
  destruct Hk as [-> Hnumeric].
  pose proof (related_rec_values eta rho T k2 vb1 vb2 vs1 vs2
      Hnumeric Hvb Hvs) as Hrec.
  destruct Hrec as [_ [_ [r1 [r2 [Her1 [Her2 Hr]]]]]].
  pose proof (value_relation_values T eta rho _ _ Hvb) as [Hvb1 Hvb2].
  pose proof (value_relation_values _ eta rho _ _ Hvs) as [Hvs1 Hvs2].
  unfold expression_relation, expression_lifting, results_match.
  split; [unfold locally_closed_tm in *; constructor; assumption |].
  split; [unfold locally_closed_tm in *; constructor; assumption |].
  exists r1, r2; repeat split; try assumption.
  - eapply rec_values_transfer; eassumption.
  - eapply rec_values_transfer; eassumption.
Qed.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof.
  intros t v H; induction H; eauto with core.
  constructor; constructor; assumption.
Qed.

Lemma evaluates_closed : forall t v, evaluates t v -> locally_closed_tm t.
Proof.
  intros t v H; induction H; try assumption;
    unfold locally_closed_tm in *; eauto with core.
  apply value_closed; assumption.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; induction H; intros Huv; eauto using multi_step.
Qed.

Lemma multi_app_left : forall t u arg,
  t -->* u -> locally_closed_tm arg -> tm_app t arg -->* tm_app u arg.
Proof.
  intros t u arg H; induction H; intros Harg.
  - constructor.
  - eapply multi_step; [eapply ST_App1; eassumption | auto].
Qed.

Lemma multi_app_right : forall t u f,
  t -->* u -> value f -> tm_app f t -->* tm_app f u.
Proof.
  intros t u f H; induction H; intros Hf.
  - constructor.
  - eapply multi_step; [eapply ST_App2; eassumption | auto].
Qed.

Lemma multi_tapp : forall t u U,
  t -->* u -> locally_closed_ty U -> tm_tapp t U -->* tm_tapp u U.
Proof.
  intros t u U H; induction H; intros HU.
  - constructor.
  - eapply multi_step; [eapply ST_TApp; eassumption | auto].
Qed.

Lemma multi_succ : forall t u, t -->* u -> tm_succ t -->* tm_succ u.
Proof.
  intros t u H; induction H.
  - constructor.
  - eapply multi_step; [eapply ST_Succ; eassumption | auto].
Qed.

Lemma multi_if : forall c d t u,
  c -->* d -> locally_closed_tm t -> locally_closed_tm u ->
  tm_if c t u -->* tm_if d t u.
Proof.
  intros c d t u H; induction H; intros Ht Hu.
  - constructor.
  - eapply multi_step; [eapply ST_If; eassumption | auto].
Qed.

Lemma multi_rec_arg : forall n n' b s,
  n -->* n' -> locally_closed_tm b -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n' b s.
Proof.
  intros n n' b s H; induction H; intros Hb Hs.
  - constructor.
  - eapply multi_step; [eapply ST_RecArg; eassumption | auto].
Qed.

Lemma multi_rec_base : forall b b' n s,
  b -->* b' -> numeric_value n -> locally_closed_tm s ->
  tm_natrec n b s -->* tm_natrec n b' s.
Proof.
  intros b b' n s H; induction H; intros Hn Hs.
  - constructor.
  - eapply multi_step; [eapply ST_RecBase; eassumption | auto].
Qed.

Lemma multi_rec_step : forall s s' n b,
  s -->* s' -> numeric_value n -> value b ->
  tm_natrec n b s -->* tm_natrec n b s'.
Proof.
  intros s s' n b H; induction H; intros Hn Hb.
  - constructor.
  - eapply multi_step; [eapply ST_RecStep; eassumption | auto].
Qed.

Lemma evaluates_multi : forall t v, evaluates t v -> t -->* v.
Proof.
  intros t v H; induction H.
  - apply multi_refl.
  - eapply multi_trans.
    + apply multi_app_left; [exact IHevaluates1 | eapply evaluates_closed; eassumption].
    + eapply multi_trans.
      * apply multi_app_right; [exact IHevaluates2 | eapply evaluates_value; eassumption].
      * eapply multi_step.
        -- apply ST_AppAbs; [apply value_closed; eapply evaluates_value; eassumption |
                              eapply evaluates_value; eassumption].
        -- exact IHevaluates3.
  - eapply multi_trans.
    + apply multi_tapp; eassumption.
    + eapply multi_step.
      * apply ST_TAppTabs; [apply value_closed; eapply evaluates_value; eassumption | assumption].
      * exact IHevaluates2.
  - eapply multi_trans.
    + apply multi_if; [exact IHevaluates1 | eapply evaluates_closed; eassumption | assumption].
    + eapply multi_step; [apply ST_IfTrue; [eapply evaluates_closed; eassumption | assumption] | exact IHevaluates2].
  - eapply multi_trans.
    + apply multi_if; [exact IHevaluates1 | assumption | eapply evaluates_closed; eassumption].
    + eapply multi_step; [apply ST_IfFalse; [assumption | eapply evaluates_closed; eassumption] | exact IHevaluates2].
  - apply multi_succ; exact IHevaluates.
  - eapply multi_trans.
    + apply multi_rec_arg; [exact IHevaluates1 | eapply evaluates_closed; eassumption | eapply evaluates_closed; eassumption].
    + eapply multi_trans.
      * apply multi_rec_base; [exact IHevaluates2 | constructor | eapply evaluates_closed; eassumption].
      * eapply multi_trans.
        -- apply multi_rec_step; [exact IHevaluates3 | constructor | eapply evaluates_value; eassumption].
        -- eapply multi_step; [apply ST_RecZero; eapply evaluates_value; eassumption | apply multi_refl].
  - eapply multi_trans.
    + apply multi_rec_arg; [exact IHevaluates1 | eapply evaluates_closed; eassumption | eapply evaluates_closed; eassumption].
    + eapply multi_trans.
      * apply multi_rec_base; [exact IHevaluates2 | constructor; assumption | eapply evaluates_closed; eassumption].
      * eapply multi_trans.
        -- apply multi_rec_step; [exact IHevaluates3 | constructor; assumption | eapply evaluates_value; eassumption].
        -- eapply multi_step; [apply ST_RecSucc; eauto using evaluates_value | exact IHevaluates4].
Qed.

Definition singleton_candidate (v : tm) (Hv : value v) : binary_candidate.
Proof.
  refine {| candidate_relation := fun left right => left = v /\ right = v |}.
  intros left right [-> ->]; auto.
Defined.

Lemma identity_from_parametricity : forall t U v rho,
  expression_relation [] rho
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) t t ->
  locally_closed_ty U -> value v -> tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t U v rho Hexpr HU Hv.
  unfold expression_relation, expression_lifting, results_match in Hexpr.
  destruct Hexpr as [_ [_ [f1 [f2 [Ht [_ Hrel]]]]]].
  simpl in Hrel.
  destruct Hrel as [_ [_ [body1 [body2 [-> [_ Hbody]]]]]].
  specialize (Hbody U U (singleton_candidate v Hv) HU HU).
  destruct Hbody as [_ [_ [g1 [g2 [Hg [_ Harrow]]]]]].
  simpl in Harrow.
  destruct Harrow as [_ [_ [A1 [term1 [A2 [term2 [-> [_ Hterm]]]]]]]].
  specialize (Hterm v v (conj eq_refl eq_refl)).
  destruct Hterm as [_ [_ [result1 [result2 [Hresult [_ [-> _]]]]]]].
  apply evaluates_multi.
  eapply EvalApp with (U := A1) (body := term1) (v := v).
  - eapply EvalTApp with (body := body1).
    + exact Ht.
    + exact HU.
    + exact Hg.
  - constructor; assumption.
  - exact Hresult.
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
  (* Complete the proof of the free theorem. *)
Qed.

End SystemFParametricityIfRecursionMediumTask.
