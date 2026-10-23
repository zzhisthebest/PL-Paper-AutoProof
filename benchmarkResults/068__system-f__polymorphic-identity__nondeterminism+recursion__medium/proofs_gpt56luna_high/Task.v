(** System F parametricity benchmark, Medium variant.
    Features: nondeterminism-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNondeterminismRecursionMediumTask.

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
      evaluates (tm_natrec n b s) result
  | EvalChoiceLeft : forall t1 t2 v,
      evaluates t1 v -> locally_closed_tm t2 -> evaluates (tm_choice t1 t2) v
  | EvalChoiceRight : forall t1 t2 v,
      locally_closed_tm t1 -> evaluates t2 v -> evaluates (tm_choice t1 t2) v.

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

Lemma and_iff : forall A A' B B' : Prop,
  (A <-> A') -> (B <-> B') -> (A /\ B <-> A' /\ B').
Proof. firstorder. Qed.

Lemma expression_lifting_iff : forall R R' t1 t2,
  (forall v1 v2, R v1 v2 <-> R' v1 v2) ->
  expression_lifting R t1 t2 <-> expression_lifting R' t1 t2.
Proof.
  intros R R' t1 t2 H; unfold expression_lifting, results_match.
  split; intros [Hlc1 [Hlc2 [v1 [v2 [He1 [He2 Hr]]]]]].
  - repeat split; try assumption.
    exists v1, v2; repeat split; try assumption.
    apply (proj1 (H v1 v2)); exact Hr.
  - repeat split; try assumption.
    exists v1, v2; repeat split; try assumption.
    apply (proj2 (H v1 v2)); exact Hr.
Qed.

Definition relation_ok (eta : list binary_candidate) (rho : binary_env) : Prop :=
  (forall i a, nth_error eta i = Some a ->
    forall v1 v2, candidate_relation a v1 v2 ->
      value v1 /\ value v2) /\
  (forall X a, rho X = Some a ->
    forall v1 v2, candidate_relation a v1 v2 ->
      value v1 /\ value v2).

Lemma value_relation_values : forall eta rho T v1 v2,
  relation_ok eta rho ->
  value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  intros eta rho T v1 v2 [He Hr] H; induction T as [i|X|T1 IH1 T2 IH2|T IH|].
  - destruct (nth_error eta i) as [c|] eqn:E; simpl in H.
    + rewrite E in H; simpl in H.
      apply (He i c E v1 v2 H).
    + rewrite E in H; simpl in H; contradiction.
  - destruct (rho X) as [c|] eqn:E; simpl in H.
    + rewrite E in H; simpl in H.
      apply (Hr X c E v1 v2 H).
    + rewrite E in H; simpl in H; contradiction.
  - simpl in H; destruct H as [H1 [H2 H]]; tauto.
  - simpl in H; destruct H as [H1 [H2 H]]; tauto.
  - simpl in H; destruct H as [Heq Hnum]; subst v2; split; apply v_nat; exact Hnum.
Qed.

Lemma relation_ok_update : forall eta rho a,
  relation_ok eta rho ->
  relation_ok (a :: eta) rho.
Proof.
  intros eta rho a [He Hr]; split.
  - intros i c E v1 v2 Hc. destruct i; simpl in E.
    + inversion E; subst c; exact (candidate_values a v1 v2 Hc).
    + eapply He; eauto.
  - exact Hr.
Qed.

Lemma relation_ok_rho_update : forall eta rho X a,
  relation_ok eta rho ->
  (forall v1 v2, candidate_relation a v1 v2 -> value v1 /\ value v2) ->
  relation_ok eta (relation_update rho X a).
Proof.
  intros eta rho X a [He Hr] Ha; split; [exact He|].
  intros Y c E v1 v2 Hc. unfold relation_update in E.
  destruct (Nat.eqb X Y) eqn:Q.
  - inversion E; subst; exact (Ha v1 v2 Hc).
  - eapply Hr; eauto.
Qed.

Lemma results_match_app : forall eta rho A B f1 f2 a1 a2,
  relation_ok eta rho ->
  results_match (value_relation eta rho (Ty_Arrow A B)) f1 f2 ->
  results_match (value_relation eta rho A) a1 a2 ->
  results_match (value_relation eta rho B) (tm_app f1 a1) (tm_app f2 a2).
Proof.
  intros eta rho A B f1 f2 a1 a2 Hok
    [vf1 [vf2 [Ef1 [Ef2 Hf]]]] [va1 [va2 [Ea1 [Ea2 Ha]]]].
  simpl in Hf; destruct Hf as [Vf1 [Vf2 [U1 [b1 [U2 [b2 [-> [-> Hfun]]]]]]]].
  simpl in Ha.
  destruct (Hfun va1 va2 Ha) as [L1 [L2 [vr1 [vr2 [Er1 [Er2 Hr]]]]]].
  exists vr1, vr2; repeat split.
  - eapply EvalApp; eauto.
  - eapply EvalApp; eauto.
  - exact Hr.
Qed.

Lemma results_match_choice : forall eta rho T t1 t2 u1 u2,
  results_match (value_relation eta rho T) t1 t2 ->
  locally_closed_tm u1 -> locally_closed_tm u2 ->
  results_match (value_relation eta rho T) (tm_choice t1 u1) (tm_choice t2 u2).
Proof.
  intros eta rho T t1 t2 u1 u2 [v1 [v2 [E1 [E2 R1]]]] Hlc1 Hlc2.
  exists v1, v2; repeat split.
  - apply EvalChoiceLeft; [exact E1|exact Hlc1].
  - apply EvalChoiceLeft; [exact E2|exact Hlc2].
  - exact R1.
Qed.

Lemma results_match_succ : forall eta rho t1 t2,
  results_match (value_relation eta rho Ty_Nat) t1 t2 ->
  results_match (value_relation eta rho Ty_Nat)
    (tm_succ t1) (tm_succ t2).
Proof.
  intros eta rho t1 t2 [n1 [n2 [E1 [E2 [He Hnum]]]]].
  subst n2; exists (tm_succ n1), (tm_succ n1); repeat split.
  - eapply EvalSucc; eauto.
  - eapply EvalSucc; eauto.
  - constructor; exact Hnum.
Qed.

(* Simultaneous substitution for the (named) term variables in a context. *)
Fixpoint subst_env (g : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => g x
  | tm_abs T t1 => tm_abs T (subst_env g t1)
  | tm_app t1 t2 => tm_app (subst_env g t1) (subst_env g t2)
  | tm_tabs t1 => tm_tabs (subst_env g t1)
  | tm_tapp t1 T => tm_tapp (subst_env g t1) T
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (subst_env g t1)
  | tm_natrec n b s => tm_natrec (subst_env g n) (subst_env g b) (subst_env g s)
  | tm_choice t1 t2 => tm_choice (subst_env g t1) (subst_env g t2)
  end.

Fixpoint ty_fv (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_fv T1 ++ ty_fv T2
  | Ty_All T1 => ty_fv T1
  | Ty_Nat => []
  end.

Fixpoint tm_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => tm_fv t1
  | tm_app t1 t2 => tm_fv t1 ++ tm_fv t2
  | tm_tabs t1 => tm_fv t1
  | tm_tapp t1 _ => tm_fv t1
  | tm_zero => []
  | tm_succ t1 => tm_fv t1
  | tm_natrec n b s => tm_fv n ++ tm_fv b ++ tm_fv s
  | tm_choice t1 t2 => tm_fv t1 ++ tm_fv t2
  end.

Fixpoint tm_ty_fv (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T t1 => ty_fv T ++ tm_ty_fv t1
  | tm_app t1 t2 => tm_ty_fv t1 ++ tm_ty_fv t2
  | tm_tabs t1 => tm_ty_fv t1
  | tm_tapp t1 T => tm_ty_fv t1 ++ ty_fv T
  | tm_zero => []
  | tm_succ t1 => tm_ty_fv t1
  | tm_natrec n b s => tm_ty_fv n ++ tm_ty_fv b ++ tm_ty_fv s
  | tm_choice t1 t2 => tm_ty_fv t1 ++ tm_ty_fv t2
  end.

Lemma value_relation_rho_fresh : forall eta rho X a T v1 v2,
  rho X = None -> ~ In X (ty_fv T) ->
  value_relation eta rho T v1 v2 <->
  value_relation eta (relation_update rho X a) T v1 v2.
Proof.
  intros eta rho X a T v1 v2; revert eta rho X a v1 v2.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH|];
    intros eta rho X a v1 v2 HX Hnot; simpl in *.
  - reflexivity.
  - assert (Hneq : X <> Y).
    { intro E; apply Hnot; simpl; left; symmetry; exact E. }
    unfold relation_update; destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E; exfalso; apply Hneq; exact E.
    + reflexivity.
  - apply and_iff; [tauto|]. apply and_iff; [tauto|].
    split.
    + intros H; destruct H as [U1 [b1 [U2 [b2 [-> [-> H]]]]]].
      exists U1,b1,U2,b2; split; [reflexivity|]; split; [reflexivity|].
      intros p q Hp.
      assert (Hp0 : value_relation eta rho T1 p q).
      { apply (proj2 (IH1 eta rho X a p q HX
          (fun Q => Hnot (in_or_app _ _ _ (or_introl Q))))); exact Hp. }
      assert (Hiff : forall r s, value_relation eta rho T2 r s <->
        value_relation eta (relation_update rho X a) T2 r s).
      { intros r s; apply (IH2 eta rho X a r s HX).
        intro Q; apply Hnot; apply in_or_app; right; exact Q. }
      apply (proj1 (expression_lifting_iff _ _ _ _ Hiff)).
      apply H; exact Hp0.
    + intros H; destruct H as [U1 [b1 [U2 [b2 [-> [-> H]]]]]].
      exists U1,b1,U2,b2; split; [reflexivity|]; split; [reflexivity|].
      intros p q Hp.
      assert (Hp0 : value_relation eta (relation_update rho X a) T1 p q).
      { apply (proj1 (IH1 eta rho X a p q HX
          (fun Q => Hnot (in_or_app _ _ _ (or_introl Q))))); exact Hp. }
      assert (Hiff : forall r s, value_relation eta rho T2 r s <->
        value_relation eta (relation_update rho X a) T2 r s).
      { intros r s; apply (IH2 eta rho X a r s HX).
        intro Q; apply Hnot; apply in_or_app; right; exact Q. }
      apply (proj2 (expression_lifting_iff _ _ _ _ Hiff)).
      apply H; exact Hp0.
  - apply and_iff; [tauto|]. apply and_iff; [tauto|].
    split.
    + intros H; destruct H as [b1 [b2 [-> [-> H]]]].
      exists b1,b2; split; [reflexivity|]; split; [reflexivity|].
      intros U1 U2 c HU1 HU2.
      assert (Hiff : forall r s, value_relation (c :: eta) rho T r s <->
        value_relation (c :: eta) (relation_update rho X a) T r s).
      { intros r s; apply (IH (c :: eta) rho X a r s HX Hnot). }
      apply (proj1 (expression_lifting_iff _ _ _ _ Hiff)).
      apply (H U1 U2 c HU1 HU2).
    + intros H; destruct H as [b1 [b2 [-> [-> H]]]].
      exists b1,b2; split; [reflexivity|]; split; [reflexivity|].
      intros U1 U2 c HU1 HU2.
      assert (Hiff : forall r s, value_relation (c :: eta) rho T r s <->
        value_relation (c :: eta) (relation_update rho X a) T r s).
      { intros r s; apply (IH (c :: eta) rho X a r s HX Hnot). }
      apply (proj2 (expression_lifting_iff _ _ _ _ Hiff)).
      apply (H U1 U2 c HU1 HU2).
  - tauto.
Qed.

Fixpoint context_ty_fv (G : context) : list atom :=
  match G with
  | [] => []
  | (_, T) :: G' => ty_fv T ++ context_ty_fv G'
  end.

Lemma lookup_context_ty_fv : forall G x T X,
  lookup_context x G = Some T -> In X (ty_fv T) ->
  In X (context_ty_fv G).
Proof.
  intros G; induction G as [|[y U] G IH]; intros x T X Hlookup HX; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst; apply in_or_app; left; exact HX.
    + apply in_or_app; right; eapply IH; eauto.
Qed.

Fixpoint context_fv (G : context) : list atom :=
  match G with
  | [] => []
  | (x, _) :: G' => x :: context_fv G'
  end.

Definition env_related (eta : list binary_candidate) (rho : binary_env)
    (Gamma : context) (g1 g2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    expression_relation eta rho T (g1 x) (g2 x).

Fixpoint list_max (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => Nat.max x (list_max xs')
  end.

Definition fresh (xs : list atom) := S (list_max xs).

Lemma list_max_ge : forall x xs, In x xs -> x <= list_max xs.
Proof.
  intros x xs; induction xs as [|y ys IH]; simpl; intros H; try contradiction.
  destruct H as [->|H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_not_in : forall xs, ~ In (fresh xs) xs.
Proof.
  unfold fresh; intros xs H.
  pose proof (list_max_ge (S (list_max xs)) xs H); lia.
Qed.

Definition tm_update (g : atom -> tm) (x : atom) (u : tm) :=
  fun y => if Nat.eqb x y then u else g y.

Lemma env_related_rho_update : forall eta rho X a Gamma g1 g2,
  rho X = None -> ~ In X (context_ty_fv Gamma) ->
  env_related eta rho Gamma g1 g2 ->
  env_related eta (relation_update rho X a) Gamma g1 g2.
Proof.
  intros eta rho X a Gamma g1 g2 HX Hfresh Henv y T Hlookup.
  apply (proj1 (expression_lifting_iff _ _ _ _
    (fun v1 v2 => value_relation_rho_fresh eta rho X a T v1 v2 HX
      (fun Q => Hfresh (lookup_context_ty_fv Gamma y T X Hlookup Q))))).
  apply Henv; exact Hlookup.
Qed.

Lemma env_related_term_update : forall eta rho Gamma g1 g2 x p q T,
  env_related eta rho Gamma g1 g2 ->
  ~ In x (context_fv Gamma) ->
  expression_relation eta rho T p q ->
  env_related eta rho (update Gamma x T)
    (tm_update g1 x p) (tm_update g2 x q).
Proof.
  intros eta rho Gamma g1 g2 x p q T Henv Hfresh Hp y U Hlookup.
  unfold update, lookup_context in Hlookup; simpl in Hlookup.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E; subst y. inversion Hlookup; subst U.
    unfold tm_update; rewrite Nat.eqb_refl.
    exact Hp.
  - apply Nat.eqb_neq in E. unfold tm_update. assert (Hxy : Nat.eqb x y = false).
    { apply Nat.eqb_neq; intro Q; apply E; exact (eq_sym Q). }
    rewrite Hxy.
    apply Henv. exact Hlookup.
Qed.

Definition env_related_late (eta : list binary_candidate) (rho : binary_env)
    (Gamma : context) (g1 g2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    expression_relation eta rho T (g1 x) (g2 x).

Fixpoint context_fv_late (G : context) : list atom :=
  match G with
  | [] => []
  | (x, _) :: G' => x :: context_fv_late G'
  end.

Fixpoint list_max_late (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => Nat.max x (list_max_late xs')
  end.

Definition fresh_late (xs : list atom) := S (list_max_late xs).

Lemma list_max_ge_late : forall x xs, In x xs -> x <= list_max_late xs.
Proof.
  intros x xs; induction xs as [|y ys IH]; simpl; intros H; try contradiction.
  destruct H as [->|H].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_not_in_late : forall xs, ~ In (fresh_late xs) xs.
Proof.
  unfold fresh_late; intros xs H.
  pose proof (list_max_ge_late (S (list_max_late xs)) xs H); lia.
Qed.

Lemma open_tm_rec_lc : forall K k t,
  lc_tm_at K k t -> forall j u, k <= j -> open_tm_rec j u t = t.
Proof.
  intros K k t H; induction H; intros j u Hj; simpl.
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - rewrite IHlc_tm_at; [reflexivity|lia].
  - rewrite IHlc_tm_at1, IHlc_tm_at2; [reflexivity|assumption|assumption].
  - rewrite IHlc_tm_at; [reflexivity|assumption].
  - rewrite IHlc_tm_at; [reflexivity|assumption].
  - reflexivity.
  - rewrite IHlc_tm_at; [reflexivity|assumption].
  - rewrite IHlc_tm_at1, IHlc_tm_at2, IHlc_tm_at3;
      [reflexivity|assumption|assumption|assumption].
  - rewrite IHlc_tm_at1, IHlc_tm_at2;
      [reflexivity|assumption|assumption].
Qed.

Lemma subst_env_open_rec : forall g,
  (forall x, locally_closed_tm (g x)) -> forall k u t,
  subst_env g (open_tm_rec k u t) =
  open_tm_rec k (subst_env g u) (subst_env g t).
Proof.
  intros g Hg k u t; revert k u.
  induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - pose proof (open_tm_rec_lc 0 0 (g a) (Hg a) k
        (subst_env g u) (le_0_n k)) as Hclosed.
    rewrite Hclosed; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2, IHt3; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma subst_env_open : forall g t x,
  (forall y, locally_closed_tm (g y)) ->
  subst_env g (open_tm t (tm_fvar x)) =
  open_tm (subst_env g t) (g x).
Proof.
  intros; apply subst_env_open_rec; assumption.
Qed.

Lemma open_ty_rec_lc : forall k T,
  lc_ty_at k T -> forall j U, k <= j -> open_ty_rec j U T = T.
Proof.
  intros k T H; induction H; intros j U Hj; simpl.
  - destruct (Nat.eqb j i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - rewrite IHlc_ty_at1, IHlc_ty_at2; [reflexivity|assumption|assumption].
  - rewrite IHlc_ty_at; [reflexivity|lia].
  - reflexivity.
Qed.

Lemma open_tm_ty_rec_lc : forall K k t,
  lc_tm_at K k t -> forall j U, K <= j -> open_tm_ty_rec j U t = t.
Proof.
  intros K k t H; induction H; intros j U Hj; simpl.
  - reflexivity.
  - reflexivity.
  - assert (Hty : open_ty_rec j U T = T).
    { eapply (open_ty_rec_lc K T); eauto. }
    rewrite Hty, IHlc_tm_at; [reflexivity|assumption].
  - rewrite IHlc_tm_at1, IHlc_tm_at2; [reflexivity|assumption|assumption].
  - rewrite IHlc_tm_at; [reflexivity|lia].
  - assert (Hty : open_ty_rec j U T = T).
    { eapply (open_ty_rec_lc K T); eauto. }
    rewrite Hty, IHlc_tm_at; [reflexivity|assumption].
  - reflexivity.
  - rewrite IHlc_tm_at; [reflexivity|assumption].
  - rewrite IHlc_tm_at1, IHlc_tm_at2, IHlc_tm_at3;
      [reflexivity|assumption|assumption|assumption].
  - rewrite IHlc_tm_at1, IHlc_tm_at2;
      [reflexivity|assumption|assumption].
Qed.

Lemma subst_env_open_ty_rec : forall g,
  (forall x, locally_closed_tm (g x)) -> forall k t U,
  subst_env g (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (subst_env g t).
Proof.
  intros g Hg k t U; revert k U.
  induction t; intros k U; simpl.
  - reflexivity.
  - pose proof (open_tm_ty_rec_lc 0 0 (g a) (Hg a) k U (le_0_n k)) as Hclosed.
    rewrite Hclosed; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt; reflexivity.
  - reflexivity.
  - rewrite IHt; reflexivity.
  - rewrite IHt1, IHt2, IHt3; reflexivity.
  - rewrite IHt1, IHt2; reflexivity.
Qed.

Lemma subst_env_open_ty : forall g,
  (forall x, locally_closed_tm (g x)) -> forall t U,
  subst_env g (open_tm_ty t U) = open_tm_ty (subst_env g t) U.
Proof.
  intros g Hg t U; unfold open_tm_ty; apply subst_env_open_ty_rec; assumption.
Qed.

Lemma subst_env_open_rec_fresh : forall g,
  (forall y, locally_closed_tm (g y)) -> forall k t x z,
  ~ In x (tm_fv t) ->
    subst_env (fun y => if Nat.eqb x y then z else g y)
    (open_tm_rec k (tm_fvar x) t) = open_tm_rec k z (subst_env g t).
Proof.
  intros g Hg k t; revert k; induction t; intros k x z H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + apply Nat.eqb_eq in E; subst n.
      unfold subst_env, open_tm_rec; simpl; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - destruct (Nat.eqb x a) eqn:E; simpl.
    + exfalso; apply H; simpl; left; apply Nat.eqb_eq in E; symmetry; exact E.
    + pose proof (open_tm_rec_lc 0 0 (g a) (Hg a) k z (le_0_n k)) as Hclosed.
      rewrite Hclosed; reflexivity.
  - rewrite (IHt (S k) x z H); reflexivity.
  - assert (H1 : ~ In x (tm_fv t1)).
    { intro Q; apply H; apply in_or_app; left; exact Q. }
    assert (H2 : ~ In x (tm_fv t2)).
    { intro Q; apply H; apply in_or_app; right; exact Q. }
    rewrite (IHt1 k x z H1), (IHt2 k x z H2); reflexivity.
  - rewrite (IHt k x z H); reflexivity.
  - rewrite (IHt k x z H); reflexivity.
  - reflexivity.
  - rewrite (IHt k x z H); reflexivity.
  - assert (H1 : ~ In x (tm_fv t1)).
    { intro Q; apply H; apply in_or_app; left; exact Q. }
    assert (H2 : ~ In x (tm_fv t2)).
    { intro Q; apply H; apply in_or_app; right; apply in_or_app; left; exact Q. }
    assert (H3 : ~ In x (tm_fv t3)).
    { intro Q; apply H; apply in_or_app; right; apply in_or_app; right; exact Q. }
    rewrite (IHt1 k x z H1), (IHt2 k x z H2), (IHt3 k x z H3); reflexivity.
  - assert (H1 : ~ In x (tm_fv t1)).
    { intro Q; apply H; apply in_or_app; left; exact Q. }
    assert (H2 : ~ In x (tm_fv t2)).
    { intro Q; apply H; apply in_or_app; right; exact Q. }
    rewrite (IHt1 k x z H1), (IHt2 k x z H2); reflexivity.
Qed.

Lemma subst_env_open_fresh : forall g,
  (forall y, locally_closed_tm (g y)) -> forall t x z,
  ~ In x (tm_fv t) ->
    subst_env (fun y => if Nat.eqb x y then z else g y)
    (open_tm t (tm_fvar x)) = open_tm (subst_env g t) z.
Proof.
  intros; unfold open_tm; apply subst_env_open_rec_fresh; assumption.
Qed.

Definition rho_dom (Delta : ty_context) (rho : binary_env) : Prop :=
  forall X, rho X <> None -> In X Delta.

Lemma rho_dom_empty : rho_dom [] (fun _ => None).
Proof. intros X H; exfalso; apply H; reflexivity. Qed.

Lemma rho_dom_update : forall Delta rho X a,
  rho_dom Delta rho -> ~ In X Delta ->
  rho_dom (X :: Delta) (relation_update rho X a).
Proof.
  unfold rho_dom, relation_update; intros Delta rho X a Hdom Hfresh Y H.
  destruct (Nat.eqb X Y) eqn:E.
  - left; apply Nat.eqb_eq in E; exact E.
  - right; apply Hdom. intro N; apply H; exact N.
Qed.

Fixpoint insert_candidate (k : nat) (a : binary_candidate)
    (eta : list binary_candidate) : list binary_candidate :=
  match k with
  | O => a :: eta
  | S k' =>
      match eta with
      | [] => []
      | b :: eta' => b :: insert_candidate k' a eta'
      end
  end.

Lemma nth_insert_candidate : forall k a eta i,
  k <= length eta -> i < S k ->
  (i = k /\ nth_error (insert_candidate k a eta) i = Some a) \/
  (i < k /\ nth_error (insert_candidate k a eta) i = nth_error eta i).
Proof.
  induction k as [|k IH]; intros a eta i Hlen Hi.
  - left; split; [lia|destruct i; [reflexivity|exfalso; lia]].
  - destruct eta as [|b eta]; simpl in Hlen; try lia.
    destruct i as [|i].
    + right; split; [lia|reflexivity].
    + simpl in Hi. specialize (IH a eta i ltac:(lia) ltac:(lia)).
      destruct IH as [[Heq Hn]|[Hlt Hn]].
      * left; split; [lia|exact Hn].
      * right; split; [lia|exact Hn].
Qed.

Lemma ty_fv_open_relation : forall k eta rho X a T v1 v2,
  rho X = None -> ~ In X (ty_fv T) ->
  lc_ty_at (S k) T -> k <= length eta ->
  value_relation (insert_candidate k a eta) rho T v1 v2 <->
  value_relation eta (relation_update rho X a)
    (open_ty_rec k (Ty_FVar X) T) v1 v2.
Proof.
  intros k eta rho X a T; revert k eta rho X a.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH|];
    intros k eta rho X a v1 v2 HX Hnot Hlc Hlen; simpl in *.
  - assert (Hi : i < S k) by (inversion Hlc; assumption).
    pose proof (nth_insert_candidate k a eta i Hlen Hi) as Hnth.
    destruct Hnth as [[Heq Hia]|[Hlt Hia]].
    + subst i. rewrite Hia. unfold open_ty_rec; rewrite Nat.eqb_refl.
      unfold value_relation; simpl; unfold relation_update.
      assert (Hxx : Nat.eqb X X = true) by apply Nat.eqb_refl.
      rewrite Hxx; simpl; tauto.
    + assert (Hik : Nat.eqb k i = false).
      { apply Nat.eqb_neq; lia. }
      unfold open_ty_rec; rewrite Hik.
      rewrite Hia. reflexivity.
  - assert (Hneq : X <> Y).
    { intro E; apply Hnot; simpl; left; symmetry; exact E. }
    unfold open_ty_rec, relation_update; simpl.
    destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E; exfalso; apply Hneq; exact E.
    + reflexivity.
  - simpl in Hnot. apply and_iff; [tauto|].
    apply and_iff; [tauto|].
    split.
    + intros H; destruct H as [U1 [body1 [U2 [body2
        [-> [-> H]]]]]].
      exists U1, body1, U2, body2; split; [reflexivity|]; split; [reflexivity|].
      intros p q Hp.
      assert (Hp0 : value_relation (insert_candidate k a eta) rho T1 p q).
      { assert (Hn : ~ In X (ty_fv T1)).
        { intro Q; apply Hnot; apply in_or_app; left; exact Q. }
        assert (Hl : lc_ty_at (S k) T1) by (inversion Hlc; assumption).
        apply (proj2 (IH1 k eta rho X a p q HX Hn Hl Hlen)); exact Hp. }
      assert (Hiff2 : forall r s,
        value_relation (insert_candidate k a eta) rho T2 r s <->
        value_relation eta (relation_update rho X a)
          (open_ty_rec k (Ty_FVar X) T2) r s).
      { intros r s.
        assert (Hn : ~ In X (ty_fv T2)).
        { intro Q; apply Hnot; apply in_or_app; right; exact Q. }
        assert (Hl : lc_ty_at (S k) T2) by (inversion Hlc; assumption).
        apply (IH2 k eta rho X a r s HX Hn Hl Hlen). }
      apply (proj1 (expression_lifting_iff
        (value_relation (insert_candidate k a eta) rho T2)
        (value_relation eta (relation_update rho X a)
          (open_ty_rec k (Ty_FVar X) T2)) _ _ Hiff2)).
      apply H; exact Hp0.
    + intros H; destruct H as [U1 [body1 [U2 [body2
        [-> [-> H]]]]]].
      exists U1, body1, U2, body2; split; [reflexivity|]; split; [reflexivity|].
      intros p q Hp.
      assert (Hp0 : value_relation eta (relation_update rho X a)
          (open_ty_rec k (Ty_FVar X) T1) p q).
      { assert (Hn : ~ In X (ty_fv T1)).
        { intro Q; apply Hnot; apply in_or_app; left; exact Q. }
        assert (Hl : lc_ty_at (S k) T1) by (inversion Hlc; assumption).
        apply (proj1 (IH1 k eta rho X a p q HX Hn Hl Hlen)); exact Hp. }
      assert (Hiff2 : forall r s,
        value_relation (insert_candidate k a eta) rho T2 r s <->
        value_relation eta (relation_update rho X a)
          (open_ty_rec k (Ty_FVar X) T2) r s).
      { intros r s.
        assert (Hn : ~ In X (ty_fv T2)).
        { intro Q; apply Hnot; apply in_or_app; right; exact Q. }
        assert (Hl : lc_ty_at (S k) T2) by (inversion Hlc; assumption).
        apply (IH2 k eta rho X a r s HX Hn Hl Hlen). }
      apply (proj2 (expression_lifting_iff
        (value_relation (insert_candidate k a eta) rho T2)
        (value_relation eta (relation_update rho X a)
          (open_ty_rec k (Ty_FVar X) T2)) _ _ Hiff2)).
      apply H; exact Hp0.
  - simpl in Hnot. apply and_iff; [tauto|].
    apply and_iff; [tauto|].
    split.
    + intros H; destruct H as [body1 [body2 [-> [-> H]]]].
      exists body1, body2; split; [reflexivity|]; split; [reflexivity|].
      intros U1 U2 c HU1 HU2.
      assert (Hiff : forall r s,
        value_relation (insert_candidate (S k) a (c :: eta)) rho T r s <->
        value_relation (c :: eta) (relation_update rho X a)
          (open_ty_rec (S k) (Ty_FVar X) T) r s).
      { intros r s.
        apply (IH (S k) (c :: eta) rho X a r s HX Hnot).
        - inversion Hlc; assumption.
        - simpl; lia. }
      apply (proj1 (expression_lifting_iff
        (value_relation (insert_candidate (S k) a (c :: eta)) rho T)
        (value_relation (c :: eta) (relation_update rho X a)
          (open_ty_rec (S k) (Ty_FVar X) T)) _ _ Hiff)).
      apply (H U1 U2 c HU1 HU2).
    + intros H; destruct H as [body1 [body2 [-> [-> H]]]].
      exists body1, body2; split; [reflexivity|]; split; [reflexivity|].
      intros U1 U2 c HU1 HU2.
      assert (Hiff : forall r s,
        value_relation (insert_candidate (S k) a (c :: eta)) rho T r s <->
        value_relation (c :: eta) (relation_update rho X a)
          (open_ty_rec (S k) (Ty_FVar X) T) r s).
      { intros r s.
        apply (IH (S k) (c :: eta) rho X a r s HX Hnot).
        - inversion Hlc; assumption.
        - simpl; lia. }
      apply (proj2 (expression_lifting_iff
        (value_relation (insert_candidate (S k) a (c :: eta)) rho T)
        (value_relation (c :: eta) (relation_update rho X a)
          (open_ty_rec (S k) (Ty_FVar X) T)) _ _ Hiff)).
      apply (H U1 U2 c HU1 HU2).
  - tauto.
Qed.

Lemma lc_ty_open_inv : forall k T X,
  ~ In X (ty_fv T) ->
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) ->
  lc_ty_at (S k) T.
Proof.
  intros k T; revert k.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH|]; intros k X Hfresh Hlc.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst i; constructor; lia.
    + apply Nat.eqb_neq in E.
      assert (Hopen : open_ty_rec k (Ty_FVar X) (Ty_BVar i) = Ty_BVar i).
      { unfold open_ty_rec; destruct (Nat.eqb k i) eqn:E2.
        - exfalso; apply E; apply Nat.eqb_eq; exact E2.
        - reflexivity. }
      rewrite Hopen in Hlc.
      assert (Hi : i < k) by (inversion Hlc; assumption).
      apply lc_ty_bvar; lia.
  - assert (Y <> X).
    { intro E; apply Hfresh; simpl; left; exact E. }
    constructor.
  - inversion Hlc as [| |kk A B HA HB| |].
    constructor.
    + apply IH1 with (k := k) (X := X); [intro Q; apply Hfresh; apply in_or_app; left; exact Q|exact HA].
    + apply IH2 with (k := k) (X := X); [intro Q; apply Hfresh; apply in_or_app; right; exact Q|exact HB].
  - inversion Hlc as [| | |kk A HA|].
    constructor.
    apply IH with (k := S k) (X := X).
    + exact Hfresh.
    + exact HA.
  - inversion Hlc; constructor; assumption.
Qed.

Lemma lc_tm_open_inv : forall K k t x,
  ~ In x (tm_fv t) ->
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k.
  induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH| |t IH|n IHn b IHb s IHs|t1 IH1 t2 IH2];
    intros K k x Hfresh Hlc.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst i; constructor; lia.
    + apply Nat.eqb_neq in E.
      assert (Hopen : open_tm_rec k (tm_fvar x) (tm_bvar i) = tm_bvar i).
      { unfold open_tm_rec; destruct (Nat.eqb k i) eqn:E2.
        - exfalso; apply E; apply Nat.eqb_eq; exact E2.
        - reflexivity. }
      rewrite Hopen in Hlc.
      apply lc_tm_bvar; inversion Hlc; lia.
  - assert (y <> x).
    { intro E; apply Hfresh; simpl; left; exact E. }
    constructor.
  - inversion Hlc; subst.
    eapply lc_tm_abs.
    + eassumption.
    + apply IH with (K := K) (k := S k) (x := x).
      * exact Hfresh.
      * eassumption.
  - inversion Hlc; subst.
    eapply lc_tm_app.
    + apply IH1 with (K := K) (k := k) (x := x).
      * intro Q; apply Hfresh; apply in_or_app; left; exact Q.
      * eassumption.
    + apply IH2 with (K := K) (k := k) (x := x).
      * intro Q; apply Hfresh; apply in_or_app; right; exact Q.
      * eassumption.
  - inversion Hlc; subst.
    eapply lc_tm_tabs. apply IH with (K := S K) (k := k) (x := x); eauto.
  - inversion Hlc; subst.
    eapply lc_tm_tapp.
    + apply IH with (K := K) (k := k) (x := x); eauto.
    + eassumption.
  - inversion H.
  - inversion Hlc; subst.
    eapply lc_tm_succ. apply IH with (K := K) (k := k) (x := x); eauto.
  - inversion Hlc; subst.
    eapply lc_tm_rec.
    + apply IHn with (K := K) (k := k) (x := x).
      * intro Q; apply Hfresh; apply in_or_app; left; exact Q.
      * eassumption.
    + apply IHb with (K := K) (k := k) (x := x).
      * intro Q; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Q.
      * eassumption.
    + apply IHs with (K := K) (k := k) (x := x).
      * intro Q; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Q.
      * eassumption.
  - inversion Hlc; subst.
    eapply lc_tm_choice.
    + apply IH1 with (K := K) (k := k) (x := x).
      * intro Q; apply Hfresh; apply in_or_app; left; exact Q.
      * eassumption.
    + apply IH2 with (K := K) (k := k) (x := x).
      * intro Q; apply Hfresh; apply in_or_app; right; exact Q.
      * eassumption.
Qed.

Lemma lc_tm_ty_open_inv : forall K k t X,
  ~ In X (tm_ty_fv t) ->
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  intros K k t; revert K k.
  induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH| |t IH|n IHn b IHb s IHs|t1 IH1 t2 IH2];
    intros K k X Hfresh Hlc.
  - inversion Hlc; constructor; assumption.
  - constructor.
  - inversion Hlc; subst.
    eapply lc_tm_abs.
    + apply lc_ty_open_inv with (k := K) (X := X).
      * intro Q; apply Hfresh; apply in_or_app; left; exact Q.
      * eassumption.
    + apply IH with (K := K) (k := S k) (X := X).
      * intro Q; apply Hfresh; apply in_or_app; right; exact Q.
      * eassumption.
  - inversion Hlc; subst.
    eapply lc_tm_app.
    + apply IH1 with (K := K) (k := k) (X := X).
      * intro Q; apply Hfresh; apply in_or_app; left; exact Q.
      * eassumption.
    + apply IH2 with (K := K) (k := k) (X := X).
      * intro Q; apply Hfresh; apply in_or_app; right; exact Q.
      * eassumption.
  - inversion Hlc; subst.
    eapply lc_tm_tabs. apply IH with (K := S K) (k := k) (X := X).
    + exact Hfresh.
    + eassumption.
  - inversion Hlc; subst.
    eapply lc_tm_tapp.
    + apply IH with (K := K) (k := k) (X := X).
      * intro Q; apply Hfresh; apply in_or_app; left; exact Q.
      * eassumption.
    + apply lc_ty_open_inv with (k := K) (X := X).
      * intro Q; apply Hfresh; apply in_or_app; right; exact Q.
      * eassumption.
  - constructor.
  - inversion Hlc; subst.
    eapply lc_tm_succ. apply IH with (K := K) (k := k) (X := X); eauto.
  - inversion Hlc; subst.
    eapply lc_tm_rec.
    + apply IHn with (K := K) (k := k) (X := X).
      * intro Q; apply Hfresh; apply in_or_app; left; exact Q.
      * eassumption.
    + apply IHb with (K := K) (k := k) (X := X).
      * intro Q; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Q.
      * eassumption.
    + apply IHs with (K := K) (k := k) (X := X).
      * intro Q; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Q.
      * eassumption.
  - inversion Hlc; subst.
    eapply lc_tm_choice.
    + apply IH1 with (K := K) (k := k) (X := X).
      * intro Q; apply Hfresh; apply in_or_app; left; exact Q.
      * eassumption.
    + apply IH2 with (K := K) (k := k) (X := X).
      * intro Q; apply Hfresh; apply in_or_app; right; exact Q.
      * eassumption.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; revert H; revert Delta; induction T; intros Delta H.
  - inversion H.
  - constructor.
  - inversion H; constructor; [assumption|assumption].
  - inversion H as [L Delta T Hwf].
    set (X := fresh (L ++ ty_fv T)).
    assert (HXL : ~ In X L) by
      (unfold X; intro Q; apply (fresh_not_in (L ++ ty_fv T)); apply in_or_app; left; exact Q).
    assert (HXT : ~ In X (ty_fv T)) by
      (unfold X; intro Q; apply (fresh_not_in (L ++ ty_fv T)); apply in_or_app; right; exact Q).
    apply lc_ty_all.
    apply lc_ty_open_inv with (k := 0) (X := X); [exact HXT|].
    apply IHt.
    apply Hwf; exact HXL.
  - constructor.
Qed.

Lemma subst_typing_lc : forall Delta Gamma t T g,
  (forall x, locally_closed_tm (g x)) ->
  has_type Delta Gamma t T ->
  locally_closed_tm (subst_env g t).
Proof.
  intros Delta Gamma t T g Hg Hty; revert Hg; revert g; induction Hty; intros g Hg.
  - unfold subst_env; apply Hg.
  - unfold locally_closed_tm in *.
    set (x := fresh (L ++ context_fv Gamma ++ tm_fv t2)).
    assert (HxL : ~ In x L) by (unfold x; intro Q; apply (fresh_not_in (L ++ context_fv Gamma ++ tm_fv t2)); apply in_or_app; left; exact Q).
    assert (HxG : ~ In x (context_fv Gamma)) by
      (unfold x; intro Q; apply (fresh_not_in (L ++ context_fv Gamma ++ tm_fv t2)); apply in_or_app; right; apply in_or_app; left; exact Q).
    assert (Hxt : ~ In x (tm_fv t2)) by
      (unfold x; intro Q; apply (fresh_not_in (L ++ context_fv Gamma ++ tm_fv t2)); apply in_or_app; right; apply in_or_app; right; exact Q).
    assert (Hg' : forall y, locally_closed_tm (tm_update g x (tm_fvar x) y)).
    { intro y; unfold tm_update; destruct (Nat.eqb x y); [constructor|apply Hg]. }
    assert (Hblc := H1 x HxL (tm_update g x (tm_fvar x)) Hg').
    assert (Heq := subst_env_open_fresh g Hg t2 x (tm_fvar x) Hxt).
    simpl; constructor.
    + exact H.
    + apply lc_tm_open_inv with (K := 0) (k := 0) (x := x).
      * exact Hxt.
      * rewrite <- Heq. exact Hblc.
  - unfold locally_closed_tm; simpl; constructor.
    + apply H1; exact Hg.
    + apply H2; exact Hg.
  - unfold locally_closed_tm; simpl; constructor.
    + apply H1; exact Hg.
    + apply H2; exact Hg.
  - set (X := fresh (L ++ tm_ty_fv t)).
    assert (HXL : ~ In X L) by (unfold X; intro Q; apply (fresh_not_in (L ++ tm_ty_fv t)); apply in_or_app; left; exact Q).
    assert (HXt : ~ In X (tm_ty_fv t)) by
      (unfold X; intro Q; apply (fresh_not_in (L ++ tm_ty_fv t)); apply in_or_app; right; exact Q).
    assert (Hb := H0 X HXL).
    assert (Hblc := H1 g Hg).
    unfold locally_closed_tm; simpl; constructor.
    apply lc_tm_ty_open_inv with (K := 0) (k := 0) (X := X).
    + exact HXt.
    + rewrite <- (subst_env_open_ty g Hg t (Ty_FVar X)).
      exact Hblc.
  - apply H1; exact Hg.
  - apply H1; exact Hg.
  - constructor.
  - constructor. apply H1; exact Hg.
  - apply H1; exact Hg.
  - apply H1; exact Hg.
  - apply H1; exact Hg.
  - apply H2; exact Hg.
  - apply H1; exact Hg.
  - apply H2; exact Hg.
  - apply H1; exact Hg.
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

End SystemFParametricityNondeterminismRecursionMediumTask.
