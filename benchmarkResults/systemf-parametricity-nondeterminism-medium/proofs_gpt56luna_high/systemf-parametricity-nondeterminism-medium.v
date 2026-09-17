(** System F parametricity benchmark, Medium variant.
    Features: nondeterminism. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNondeterminismMediumTask.

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

Inductive evaluates : tm -> tm -> Prop :=
  | EvalValue : forall v, value v -> evaluates v v
  | EvalApp : forall f arg U body v result,
      evaluates f (tm_abs U body) -> evaluates arg v ->
      evaluates (open_tm body v) result -> evaluates (tm_app f arg) result
  | EvalTApp : forall f U body result,
      evaluates f (tm_tabs body) -> locally_closed_ty U ->
      evaluates (open_tm_ty body U) result -> evaluates (tm_tapp f U) result
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
  end.

Definition expression_relation eta rho T t1 t2 :=
  expression_lifting (value_relation eta rho T) t1 t2.

(* Substitution operations used in the fundamental theorem.  The two
   substitutions are deliberately kept separate: type variables are
   interpreted by [ty_fsubst], while term variables are interpreted by
   [tm_fsubst].  This is convenient in the type-abstraction case, where the
   two sides may be instantiated at different types. *)
Fixpoint ty_fsubst (phi : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => phi X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_fsubst phi T1) (ty_fsubst phi T2)
  | Ty_All T1 => Ty_All (ty_fsubst phi T1)
  end.

Fixpoint tm_fsubst (phi : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_fsubst phi T) (tm_fsubst phi t1)
  | tm_app t1 t2 => tm_app (tm_fsubst phi t1) (tm_fsubst phi t2)
  | tm_tabs t1 => tm_tabs (tm_fsubst phi t1)
  | tm_tapp t1 T => tm_tapp (tm_fsubst phi t1) (ty_fsubst phi T)
  | tm_choice t1 t2 => tm_choice (tm_fsubst phi t1) (tm_fsubst phi t2)
  end.

Fixpoint tm_fvar_subst (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs T (tm_fvar_subst sigma t1)
  | tm_app t1 t2 => tm_app (tm_fvar_subst sigma t1) (tm_fvar_subst sigma t2)
  | tm_tabs t1 => tm_tabs (tm_fvar_subst sigma t1)
  | tm_tapp t1 T => tm_tapp (tm_fvar_subst sigma t1) T
  | tm_choice t1 t2 => tm_choice (tm_fvar_subst sigma t1) (tm_fvar_subst sigma t2)
  end.

Definition tm_inst (phi : atom -> ty) (sigma : atom -> tm) (t : tm) : tm :=
  tm_fvar_subst sigma (tm_fsubst phi t).

Definition ty_inst (phi : atom -> ty) (T : ty) : ty := ty_fsubst phi T.

Definition candidate_of_relation (R : binary_relation)
    (h : forall v1 v2, R v1 v2 -> value v1 /\ value v2) : binary_candidate :=
  {| candidate_relation := R; candidate_values := h |}.

Definition term_env_related (eta : list binary_candidate) (rho : binary_env)
    (Gamma : context) (sigma1 sigma2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value_relation eta rho T (sigma1 x) (sigma2 x).

Definition type_env_related (eta : list binary_candidate) (rho : binary_env)
    (Delta : ty_context) : Prop :=
  forall X, In X Delta ->
    exists a, rho X = Some a.

Definition fundamental_statement :=
  forall (Delta : ty_context) (Gamma : context) (t : tm) (T : ty),
    has_type Delta Gamma t T ->
    forall (eta : list binary_candidate) (rho : binary_env)
      (phi1 phi2 : atom -> ty) (sigma1 sigma2 : atom -> tm),
      type_env_related eta rho Delta ->
      (forall X, locally_closed_ty (phi1 X)) ->
      (forall X, locally_closed_ty (phi2 X)) ->
      term_env_related eta rho Gamma sigma1 sigma2 ->
      expression_relation eta rho T
        (tm_inst phi1 sigma1 t) (tm_inst phi2 sigma2 t).

Fixpoint atoms_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => atoms_ty T1 ++ atoms_ty T2
  | Ty_All T1 => atoms_ty T1
  end.

Fixpoint atoms_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T t1 => atoms_ty T ++ atoms_tm t1
  | tm_app t1 t2 => atoms_tm t1 ++ atoms_tm t2
  | tm_tabs t1 => atoms_tm t1
  | tm_tapp t1 T => atoms_tm t1 ++ atoms_ty T
  | tm_choice t1 t2 => atoms_tm t1 ++ atoms_tm t2
  end.

Fixpoint atoms_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x,T) :: Gamma' => x :: atoms_ty T ++ atoms_context Gamma'
  end.

Fixpoint list_max (l : list atom) : atom :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (list_max l')
  end.

Lemma in_le_list_max : forall l x, In x l -> x <= list_max l.
Proof.
  induction l as [|y l IH]; simpl; intros x H.
  - contradiction.
  - destruct H as [->|H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Definition rel_equiv (R S : binary_relation) : Prop :=
  forall x y, R x y <-> S x y.

Lemma results_match_ext : forall R S t1 t2,
    rel_equiv R S -> results_match R t1 t2 <-> results_match S t1 t2.
Proof.
  intros R S t1 t2 He; split; intros [v1 [v2 [H1 [H2 HR]]]];
    exists v1, v2; repeat split; try assumption; [apply (He _ _); exact HR|apply (He _ _); exact HR].
Qed.

Lemma expression_lifting_ext : forall R S t1 t2,
    rel_equiv R S -> expression_lifting R t1 t2 <-> expression_lifting S t1 t2.
Proof.
  intros R S t1 t2 He; unfold expression_lifting; rewrite (results_match_ext R S t1 t2 He); tauto.
Qed.

Definition eta_agree (n : nat) (eta eta' : list binary_candidate) : Prop :=
  forall i, i < n -> nth_error eta i = nth_error eta' i.

Lemma eta_agree_skip : forall n a eta eta',
    eta_agree n eta eta' -> eta_agree (S n) (a :: eta) (a :: eta').
Proof.
  intros n a eta eta' H i Hi.
  destruct i as [|i].
  - reflexivity.
  - simpl. rewrite (H i); [reflexivity|lia].
Qed.

Lemma vr_eta_irrel_at : forall n T eta eta' rho,
    lc_ty_at n T -> eta_agree n eta eta' ->
    forall v1 v2, value_relation eta rho T v1 v2 <->
                   value_relation eta' rho T v1 v2.
Proof.
  intros n T eta eta' rho Hlc; revert eta eta'.
  induction Hlc as
    [k0 i Hi|k0 X|k0 T1 T2 H1 IH1 H2 IH2|k0 T H IH];
    intros eta eta' Hag v1 v2; simpl.
  - split; intro H; simpl in Hag.
    + rewrite (Hag i Hi) in H; exact H.
    + rewrite <- (Hag i Hi) in H; exact H.
  - tauto.
  - split; intros H.
    + destruct H as [Hv1 [Hv2 [U1 [b1 [U2 [b2 [E1 [E2 Hb]]]]]]]].
      split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, b1, U2, b2. split; [exact E1|]. split; [exact E2|].
      intros a1 a2 Ha.
      apply (expression_lifting_ext
        (value_relation eta rho T2) (value_relation eta' rho T2)
        (open_tm b1 a1) (open_tm b2 a2)).
      exact (IH2 eta eta' Hag).
      exact (Hb a1 a2 ((proj2 ((IH1 eta eta' Hag) a1 a2)) Ha)).
    + destruct H as [Hv1 [Hv2 [U1 [b1 [U2 [b2 [E1 [E2 Hb]]]]]]]].
      split; [exact Hv1|]. split; [exact Hv2|].
      exists U1, b1, U2, b2. split; [exact E1|]. split; [exact E2|].
      intros a1 a2 Ha.
      apply (expression_lifting_ext
        (value_relation eta' rho T2) (value_relation eta rho T2)
        (open_tm b1 a1) (open_tm b2 a2)).
      exact (IH2 eta' eta (fun i Hi => eq_sym (Hag i Hi))).
      exact (Hb a1 a2 ((proj1 ((IH1 eta eta' Hag) a1 a2)) Ha)).
  - split; intros Hrel.
    + destruct Hrel as [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hb]]]]]].
      split; [exact Hv1|]. split; [exact Hv2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros A B c HA HB.
      apply (expression_lifting_ext
        (value_relation (c :: eta) rho T)
        (value_relation (c :: eta') rho T)
        (open_tm_ty b1 A) (open_tm_ty b2 B)).
      exact (IH (c :: eta) (c :: eta') (eta_agree_skip k0 c eta eta' Hag)).
      exact (Hb A B c HA HB).
    + destruct Hrel as [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hb]]]]]].
      split; [exact Hv1|]. split; [exact Hv2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros A B c HA HB.
      apply (expression_lifting_ext
        (value_relation (c :: eta') rho T)
        (value_relation (c :: eta) rho T)
        (open_tm_ty b1 A) (open_tm_ty b2 B)).
      exact (IH (c :: eta') (c :: eta)
        (eta_agree_skip k0 c eta' eta (fun i Hi => eq_sym (Hag i Hi)))).
      exact (Hb A B c HA HB).
Qed.

Fixpoint eta_insert (k : nat) (a : binary_candidate)
    (eta : list binary_candidate) : list binary_candidate :=
  match k, eta with
  | 0, _ => a :: eta
  | S k', [] => a :: []
  | S k', b :: eta' => b :: eta_insert k' a eta'
  end.

Lemma nth_eta_insert_lt : forall k a eta i,
    k <= length eta -> i < k ->
    nth_error (eta_insert k a eta) i = nth_error eta i.
Proof.
  induction k as [|k IH]; intros a eta i Hlen Hi; [lia|].
  destruct eta as [|b eta]; simpl.
  - simpl in Hlen; lia.
  - destruct i as [|i]; simpl.
    + reflexivity.
    + apply IH; [simpl in Hlen; lia|lia].
Qed.

Lemma nth_eta_insert_eq : forall k a eta,
    k <= length eta -> nth_error (eta_insert k a eta) k = Some a.
Proof.
  induction k as [|k IH]; intros a eta Hlen; simpl; [reflexivity|].
  destruct eta as [|b eta]; simpl.
  - simpl in Hlen; lia.
  - apply IH; simpl in Hlen; lia.
Qed.

Lemma eta_insert_succ_cons : forall k a c eta,
    eta_insert (S k) a (c :: eta) = c :: eta_insert k a eta.
Proof. reflexivity. Qed.

Lemma lc_ty_bvar_bound : forall k i,
    lc_ty_at k (Ty_BVar i) -> i < k.
Proof. intros k i H; inversion H; assumption. Qed.

Lemma vr_open_rec : forall k T U a eta rho,
    lc_ty_at (S k) T -> locally_closed_ty U -> k <= length eta ->
    (forall x y, a.(candidate_relation) x y <->
                 value_relation eta rho U x y) ->
    forall v1 v2,
      value_relation eta rho (open_ty_rec k U T) v1 v2 <->
      value_relation (eta_insert k a eta) rho T v1 v2.
Proof.
  intros k T; revert k.
  induction T as [i|X|T1 IH1 T2 IH2|T IH];
    intros d U a eta rho Hlc HU Hlen Ha v1 v2; simpl.
  - assert (Hi : i < S d) by (apply lc_ty_bvar_bound; exact Hlc).
    destruct (Nat.eqb_spec d i) as [->|Hne].
    + rewrite (nth_eta_insert_eq i a eta Hlen).
      split; intro H; [apply (proj2 (Ha _ _)); exact H|apply (proj1 (Ha _ _)); exact H].
    + assert (Hid : i < d) by lia.
      rewrite (nth_eta_insert_lt d a eta i Hlen Hid); reflexivity.
  - tauto.
  - assert (H1 : lc_ty_at (S d) T1) by (inversion Hlc; assumption).
    assert (H2 : lc_ty_at (S d) T2) by (inversion Hlc; assumption).
    split; intros Hrel.
    + destruct Hrel as [Hv1 [Hv2 [W1 [b1 [W2 [b2 [E1 [E2 Hb]]]]]]]].
      split; [exact Hv1|]. split; [exact Hv2|].
      exists W1, b1, W2, b2. split; [exact E1|]. split; [exact E2|].
      intros x y Hxy.
      apply (expression_lifting_ext
        (value_relation (eta_insert d a eta) rho T2)
        (value_relation eta rho (open_ty_rec d U T2))
        (open_tm b1 x) (open_tm b2 y)
        (fun p q => iff_sym (IH2 d U a eta rho H2 HU Hlen Ha p q))).
      exact (Hb x y (proj2 (IH1 d U a eta rho H1 HU Hlen Ha x y) Hxy)).
    + destruct Hrel as [Hv1 [Hv2 [W1 [b1 [W2 [b2 [E1 [E2 Hb]]]]]]]].
      split; [exact Hv1|]. split; [exact Hv2|].
      exists W1, b1, W2, b2. split; [exact E1|]. split; [exact E2|].
      intros x y Hxy.
      apply (expression_lifting_ext
        (value_relation eta rho (open_ty_rec d U T2))
        (value_relation (eta_insert d a eta) rho T2)
        (open_tm b1 x) (open_tm b2 y)
        (IH2 d U a eta rho H2 HU Hlen Ha)).
      exact (Hb x y (proj1 (IH1 d U a eta rho H1 HU Hlen Ha x y) Hxy)).
  - assert (H : lc_ty_at (S (S d)) T) by (inversion Hlc; assumption).
    split; intros Hrel.
    + destruct Hrel as [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hb]]]]]].
      split; [exact Hv1|]. split; [exact Hv2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros A B c HA HB.
      assert (Hac : forall x y, candidate_relation a x y <->
        value_relation (c :: eta) rho U x y) by
        (intros x y;
         rewrite <- (vr_eta_irrel_at 0 U eta (c :: eta) rho HU
           (fun i Hi => False_rect _ (Nat.nlt_0_r i Hi)) x y); exact (Ha x y)).
      assert (He : forall p q,
        value_relation (c :: eta) rho (open_ty_rec (S d) U T) p q <->
        value_relation (eta_insert (S d) a (c :: eta)) rho T p q) by
      (intros p q; rewrite eta_insert_succ_cons;
          apply (IH (S d) U a (c :: eta) rho H HU (le_n_S _ _ Hlen) Hac p q)).
      apply (expression_lifting_ext
        (value_relation (c :: eta) rho (open_ty_rec (S d) U T))
        (value_relation (eta_insert (S d) a (c :: eta)) rho T)
        (open_tm_ty b1 A) (open_tm_ty b2 B) He).
      exact (Hb A B c HA HB).
    + destruct Hrel as [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hb]]]]]].
      split; [exact Hv1|]. split; [exact Hv2|].
      exists b1, b2. split; [exact E1|]. split; [exact E2|].
      intros A B c HA HB.
      assert (Hac : forall x y, candidate_relation a x y <->
        value_relation (c :: eta) rho U x y) by
        (intros x y;
         rewrite <- (vr_eta_irrel_at 0 U eta (c :: eta) rho HU
           (fun i Hi => False_rect _ (Nat.nlt_0_r i Hi)) x y); exact (Ha x y)).
      assert (He : forall p q,
        value_relation (eta_insert (S d) a (c :: eta)) rho T p q <->
        value_relation (c :: eta) rho (open_ty_rec (S d) U T) p q) by
      (intros p q; rewrite eta_insert_succ_cons; symmetry;
          apply (IH (S d) U a (c :: eta) rho H HU (le_n_S _ _ Hlen) Hac p q)).
      apply (expression_lifting_ext
        (value_relation (eta_insert (S d) a (c :: eta)) rho T)
        (value_relation (c :: eta) rho (open_ty_rec (S d) U T))
        (open_tm_ty b1 A) (open_tm_ty b2 B) He).
      exact (Hb A B c HA HB).
Qed.

Lemma vr_values_wf : forall Delta T eta rho v1 v2,
    wf_ty Delta T -> type_env_related eta rho Delta ->
    value_relation eta rho T v1 v2 -> value v1 /\ value v2.
Proof.
  intros Delta T eta rho v1 v2 Hwf; induction Hwf using wf_ty_ind;
    intros Henv Hrel; simpl in Hrel.
  - destruct (Henv X H) as [a Ea]. rewrite Ea in Hrel.
    apply (candidate_values a v1 v2 Hrel).
  - tauto.
  - tauto.
Qed.

Lemma lookup_update_fresh : forall Gamma x T,
    ~ In x (atoms_context Gamma) ->
    lookup_context x (update Gamma x T) = Some T.
Proof. intros; simpl; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma lookup_update_other : forall Gamma x y T,
    ~ In x (atoms_context Gamma) -> x <> y ->
    lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x y T Hfresh Hxy. simpl.
  destruct (Nat.eqb_spec y x) as [->|Hne]; [contradiction|reflexivity].
Qed.

Lemma type_env_related_update : forall eta rho Delta X a,
    type_env_related eta rho Delta -> ~ In X Delta ->
    type_env_related eta (relation_update rho X a) (X :: Delta).
Proof.
  intros eta rho Delta X a H Hn Y HY.
  simpl in HY. destruct HY as [->|HY].
  - exists a. unfold relation_update. rewrite Nat.eqb_refl. reflexivity.
  - destruct (H Y HY) as [b Hb]. exists b. unfold relation_update.
    destruct (Nat.eqb_spec X Y); [subst; contradiction|exact Hb].
Qed.

Lemma vr_rho_update_irrel : forall n T eta rho X a,
    lc_ty_at n T -> ~ In X (atoms_ty T) ->
    forall v1 v2,
      value_relation eta (relation_update rho X a) T v1 v2 <->
      value_relation eta rho T v1 v2.
Proof.
  intros n T eta rho X a Hlc; revert eta rho X a.
  induction Hlc as [k i Hi|k Y|k T1 T2 H1 IH1 H2 IH2|k T H IH];
    intros eta rho X a Hfresh v1 v2; simpl.
  - tauto.
  - destruct (Nat.eqb_spec X Y) as [->|Hne].
    + exfalso. apply Hfresh. simpl; auto.
    + unfold relation_update. destruct (Nat.eqb X Y) eqn:E.
      * exfalso. apply Hne. apply Nat.eqb_eq; exact E.
      * tauto.
  - assert (F1 : ~ In X (atoms_ty T1)).
    { intro h; apply Hfresh; apply in_or_app; left; exact h. }
    assert (F2 : ~ In X (atoms_ty T2)).
    { intro h; apply Hfresh; apply in_or_app; right; exact h. }
    split; intros Hrel.
    + destruct Hrel as [Hv1 [Hv2 [W1 [b1 [W2 [b2 [E1 [E2 Hb]]]]]]]].
      split; [exact Hv1|]. split; [exact Hv2|].
      exists W1,b1,W2,b2; split; [exact E1|]. split; [exact E2|].
      intros x y Hxy.
      apply (expression_lifting_ext
        (value_relation eta rho T2)
        (value_relation eta (relation_update rho X a) T2)
        (open_tm b1 x) (open_tm b2 y)).
      exact (fun p q => iff_sym (IH2 eta rho X a F2 p q)).
      exact (Hb x y (proj2 (IH1 eta rho X a F1 x y) Hxy)).
    + destruct Hrel as [Hv1 [Hv2 [W1 [b1 [W2 [b2 [E1 [E2 Hb]]]]]]]].
      split; [exact Hv1|]. split; [exact Hv2|].
      exists W1,b1,W2,b2; split; [exact E1|]. split; [exact E2|].
      intros x y Hxy.
      apply (expression_lifting_ext
        (value_relation eta (relation_update rho X a) T2)
        (value_relation eta rho T2)
        (open_tm b1 x) (open_tm b2 y)).
      exact (IH2 eta rho X a F2).
      exact (Hb x y (proj1 (IH1 eta rho X a F1 x y) Hxy)).
  - assert (F : ~ In X (atoms_ty T)).
    { intro h; apply Hfresh; exact h. }
    split; intros Hrel.
    + destruct Hrel as [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hb]]]]]].
      split; [exact Hv1|]. split; [exact Hv2|]. exists b1,b2.
      split; [exact E1|]. split; [exact E2|].
      intros A B c HA HB.
      apply (expression_lifting_ext
        (value_relation (c::eta) rho T)
        (value_relation (c::eta) (relation_update rho X a) T)
        (open_tm_ty b1 A) (open_tm_ty b2 B)).
      exact (fun p q => iff_sym (IH (c::eta) rho X a F p q)).
      exact (Hb A B c HA HB).
    + destruct Hrel as [Hv1 [Hv2 [b1 [b2 [E1 [E2 Hb]]]]]].
      split; [exact Hv1|]. split; [exact Hv2|]. exists b1,b2.
      split; [exact E1|]. split; [exact E2|].
      intros A B c HA HB.
      apply (expression_lifting_ext
        (value_relation (c::eta) (relation_update rho X a) T)
        (value_relation (c::eta) rho T)
        (open_tm_ty b1 A) (open_tm_ty b2 B)).
      exact (IH (c::eta) rho X a F).
      exact (Hb A B c HA HB).
Qed.

Lemma vr_open_fvar : forall T eta rho X a,
    lc_ty_at 1 T -> ~ In X (atoms_ty T) ->
    forall v1 v2,
      value_relation eta (relation_update rho X a) (open_ty T (Ty_FVar X)) v1 v2 <->
      value_relation (a :: eta) rho T v1 v2.
Proof.
  intros T eta rho X a Hlc Hfresh v1 v2.
  assert (Ha : forall x y, candidate_relation a x y <->
    value_relation eta (relation_update rho X a) (Ty_FVar X) x y).
  { intros x y. unfold value_relation, relation_update.
    destruct (Nat.eqb_spec X X); tauto. }
  pose proof (vr_open_rec 0 T (Ty_FVar X) a eta
    (relation_update rho X a) Hlc (lc_ty_fvar 0 X) (le_0_n _) Ha v1 v2) as H.
  simpl in H. rewrite (vr_rho_update_irrel 1 T (a :: eta) rho X a Hlc Hfresh v1 v2) in H.
  exact H.
Qed.

Definition fundamental_statement_lc :=
  forall (Delta : ty_context) (Gamma : context) (t : tm) (T : ty),
    has_type Delta Gamma t T -> locally_closed_tm t ->
    forall (eta : list binary_candidate) (rho : binary_env)
      (phi1 phi2 : atom -> ty) (sigma1 sigma2 : atom -> tm),
      type_env_related eta rho Delta ->
      (forall X, locally_closed_ty (phi1 X)) ->
      (forall X, locally_closed_ty (phi2 X)) ->
      (forall x, locally_closed_tm (sigma1 x)) ->
      (forall x, locally_closed_tm (sigma2 x)) ->
      term_env_related eta rho Gamma sigma1 sigma2 ->
      expression_relation eta rho T
        (tm_inst phi1 sigma1 t) (tm_inst phi2 sigma2 t).

Lemma expression_of_evaluations : forall R t1 t2 v1 v2,
    locally_closed_tm t1 -> locally_closed_tm t2 ->
    evaluates t1 v1 -> evaluates t2 v2 -> R v1 v2 ->
    expression_lifting R t1 t2.
Proof.
  intros; unfold expression_lifting, results_match; repeat split; eauto.
Qed.

Lemma evaluates_app : forall f1 f2 v1 v2 U1 U2 b1 b2 r1 r2,
    evaluates f1 (tm_abs U1 b1) -> evaluates f2 (tm_abs U2 b2) ->
    evaluates v1 r1 -> evaluates v2 r2 ->
    evaluates (open_tm b1 r1) v1 -> evaluates (open_tm b2 r2) v2 ->
    evaluates (tm_app f1 v1) v1 /\ evaluates (tm_app f2 v2) v2.
Proof.
  intros. split; eapply EvalApp; eauto.
Qed.

Lemma fresh_atom : forall l : list atom, exists x, ~ In x l.
Proof.
  intro l. exists (S (list_max l)). intro H.
  pose proof (in_le_list_max l (S (list_max l)) H). lia.
Qed.

Lemma fresh_ty : forall T, exists x, ~ In x (atoms_ty T).
Proof. intro T. apply fresh_atom. Qed.

Lemma fresh_tm : forall t, exists x, ~ In x (atoms_tm t).
Proof. intro t. apply fresh_atom. Qed.

Lemma fresh_context : forall Gamma, exists x, ~ In x (atoms_context Gamma).
Proof. intro Gamma. apply fresh_atom. Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption. Qed.

Lemma evaluates_lc : forall t v, evaluates t v -> locally_closed_tm t.
Proof.
  intros t v H; induction H; eauto using value_lc; try constructor; eauto.
Qed.

Lemma evaluates_value : forall t v, evaluates t v -> value v.
Proof.
  intros t v H; induction H; eauto.
Qed.

Lemma multi_trans : forall x y z, x -->* y -> y -->* z -> x -->* z.
Proof.
  intros x y z H; induction H; eauto using multi.
Qed.

Lemma multi_app1 : forall t1 t1' t2,
    t1 -->* t1' -> locally_closed_tm t2 ->
    tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 H; induction H; intros Hlc.
  - constructor.
  - eapply multi_step.
    + eapply ST_App1; eauto.
    + eauto.
Qed.

Lemma multi_app2 : forall v1 t2 t2',
    value v1 -> t2 -->* t2' ->
    tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros v1 t2 t2' Hv H; induction H.
  - constructor.
  - eapply multi_step.
    + eapply ST_App2; eauto.
    + eauto.
Qed.

Lemma multi_tapp : forall t t' U,
    t -->* t' -> locally_closed_ty U ->
    tm_tapp t U -->* tm_tapp t' U.
Proof.
  intros t t' U H; induction H; intros HU.
  - constructor.
  - eapply multi_step.
    + eapply ST_TApp; eauto.
    + eauto.
Qed.

Lemma evaluates_multi : forall t v, evaluates t v -> t -->* v.
Proof.
  intros t v H; induction H as
    [v Hv
    | f arg U body v result Hf IHf Ha IHa Hb IHb
    | f U body result Hf IHf HU IHbody
    | t1 t2 v H1 IH1 H2
    | t1 t2 v H1 H2 IH2
    ].
  - constructor.
  - eapply multi_trans.
    + eapply multi_app1; [exact IHf|apply evaluates_lc with (v:=v); exact Ha].
    + eapply multi_trans.
      * eapply multi_app2; [apply evaluates_value with (t:=f); exact Hf|exact IHa].
      * eapply multi_step.
        -- eapply ST_AppAbs.
           ++ apply value_lc. apply evaluates_value with (t:=f). exact Hf.
           ++ apply evaluates_value with (t:=arg); exact Ha.
        -- exact IHb.
  - eapply multi_trans.
    + eapply multi_tapp; [exact IHf|exact HU].
    + eapply multi_step.
      * eapply ST_TAppTabs; [apply value_lc; apply evaluates_value with (t:=f); exact Hf|exact HU].
      * exact IHIHbody.
  - eapply multi_trans.
    + eapply multi_step; [eapply ST_ChoiceLeft; [apply evaluates_lc with (v:=v); exact H1|exact H2]|].
      exact IH1.
    + constructor.
  - eapply multi_trans.
    + eapply multi_step; [eapply ST_ChoiceRight; [exact H1|apply evaluates_lc with (v:=v); exact H2]|].
      exact IH2.
    + constructor.
Qed.

Lemma lc_ty_weaken : forall k T, lc_ty_at k T -> lc_ty_at (S k) T.
Proof.
  intros k T H; induction H; eauto using lc_ty_at; lia.
Qed.

Lemma lc_tm_weaken_term : forall K k t, lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H; induction H; eauto using lc_tm_at; lia.
Qed.

Lemma lc_tm_weaken_type : forall K k t, lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H; induction H; eauto using lc_tm_at, lc_ty_weaken; lia.
Qed.

Lemma lc_ty_fsubst : forall K T phi,
    lc_ty_at K T -> (forall X, lc_ty_at K (phi X)) ->
    lc_ty_at K (ty_fsubst phi T).
Proof.
  intros K T phi H; induction H; intros Hphi; simpl; eauto using lc_ty_at, lc_ty_weaken.
Qed.

Lemma lc_tm_fsubst : forall K k t phi,
    lc_tm_at K k t -> (forall X, lc_ty_at K (phi X)) ->
    lc_tm_at K k (tm_fsubst phi t).
Proof.
  intros K k t phi H; induction H; intros Hphi; simpl; eauto using lc_tm_at, lc_ty_fsubst; try solve [apply IHlc_tm_at; intros; apply lc_ty_weaken; apply Hphi].
  all: constructor; apply IHlc_tm_at; intro X; apply lc_ty_weaken; apply Hphi.
Qed.

Lemma lc_tm_fvar_subst : forall K k t sigma,
    lc_tm_at K k t -> (forall x, lc_tm_at K k (sigma x)) ->
    lc_tm_at K k (tm_fvar_subst sigma t).
Proof.
  intros K k t sigma H; induction H; intros Hsig; simpl; eauto using lc_tm_at.
  all: try solve [constructor; eauto; apply IHlc_tm_at; intros; apply lc_tm_weaken_term; apply Hsig].
  all: constructor; apply IHlc_tm_at; intro; apply lc_tm_weaken_type; apply Hsig.
Qed.

Lemma lc_tm_inst : forall t phi sigma,
    locally_closed_tm t ->
    (forall X, locally_closed_ty (phi X)) ->
    (forall x, locally_closed_tm (sigma x)) ->
    locally_closed_tm (tm_inst phi sigma t).
Proof.
  intros t phi sigma H Hphi Hsig.
  unfold tm_inst.
  apply lc_tm_fvar_subst with (K:=0) (k:=0).
  - apply lc_tm_fsubst with (K:=0) (k:=0); assumption.
  - exact Hsig.
Qed.

Lemma lc_ty_open_rec : forall k T U,
    lc_ty_at (S k) T -> lc_ty_at k U ->
    lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k T U H Ulc. revert k U H Ulc.
  induction T as [i|X|T1 IH1 T2 IH2|T IH];
    intros k U H Ulc; simpl in *.
  - destruct (Nat.eqb_spec k i) as [->|Hne].
    + exact Ulc.
    + constructor. inversion H; lia.
  - constructor.
  - inversion H; constructor; [eapply IH1|eapply IH2]; eauto.
  - inversion H; constructor; eapply IH; eauto using lc_ty_weaken.
Qed.

Lemma lc_ty_open_rec_inv : forall k T U,
    lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  intros k T U H. revert k U H.
  induction T as [i|X|T1 IH1 T2 IH2|T IH];
    intros k U H; simpl in *.
  - destruct (Nat.eqb_spec k i) as [->|Hne].
    + constructor; lia.
    + inversion H; constructor; lia.
  - constructor.
  - inversion H; constructor; [eapply IH1|eapply IH2]; eauto.
  - inversion H; constructor; eapply IH; eauto.
Qed.

Lemma lc_tm_open_rec : forall K k t u,
    lc_tm_at K (S k) t -> lc_tm_at K k u ->
    lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t u H Ulc. revert K k u H Ulc.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH|t1 IH1 t2 IH2];
    intros K k u H Ulc; simpl in *.
  - destruct (Nat.eqb_spec k i) as [->|Hne].
    + exact Ulc.
    + constructor. inversion H; lia.
  - constructor.
  - inversion H; constructor.
    + assumption.
    + eapply IH; eauto using lc_tm_weaken_term.
  - inversion H; constructor; [eapply IH1|eapply IH2]; eauto.
  - inversion H; constructor; eapply IH; eauto using lc_tm_weaken_type.
  - inversion H; constructor; [eapply IH|assumption]; eauto.
  - inversion H; constructor; [eapply IH1|eapply IH2]; eauto.
Qed.

Lemma lc_tm_open_rec_inv : forall K k t u,
    lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k t u H. revert K k u H.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH|t1 IH1 t2 IH2];
    intros K k u H; simpl in *.
  - destruct (Nat.eqb_spec k i) as [->|Hne].
    + constructor; lia.
    + inversion H; constructor; lia.
  - constructor.
  - inversion H; constructor; [assumption|eapply IH; eauto].
  - inversion H; constructor; [eapply IH1|eapply IH2]; eauto.
  - inversion H; constructor; eapply IH; eauto.
  - inversion H; constructor; [eapply IH|assumption]; eauto.
  - inversion H; constructor; [eapply IH1|eapply IH2]; eauto.
Qed.

Lemma lc_tm_ty_open_rec_inv : forall K k t U,
    lc_tm_at K k (open_tm_ty_rec K U t) -> lc_tm_at (S K) k t.
Proof.
  intros K k t U H. revert K k U H.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH|t1 IH1 t2 IH2];
    intros K k U H; simpl in *.
  - constructor. inversion H; assumption.
  - constructor.
  - inversion H; constructor; [eapply lc_ty_open_rec_inv|eapply IH]; eauto.
  - inversion H; constructor; [eapply IH1|eapply IH2]; eauto.
  - inversion H; constructor; eapply IH; eauto.
  - inversion H; constructor; [eapply IH|eapply lc_ty_open_rec_inv]; eauto.
  - inversion H; constructor; [eapply IH1|eapply IH2]; eauto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H using wf_ty_ind; unfold locally_closed_ty in *; eauto using lc_ty_at.
  apply lc_ty_all.
  destruct (fresh_atom L) as [X HX].
  apply lc_ty_open_rec_inv with (U:=Ty_FVar X).
  eauto.
Qed.

Lemma typing_lc : forall Delta Gamma t T,
    has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H.
  refine (has_type_ind
    (fun Delta Gamma t T => locally_closed_tm t) _ _ _ _ _ _
    Delta Gamma t T H).
  - intros D G x T0 Hlookup Hwf. constructor.
  - intros L D G T1 t2 T2 Hwf Hbody IHbody.
    apply lc_tm_abs.
    + eapply wf_ty_lc; eassumption.
    + destruct (fresh_atom (L ++ atoms_tm t2 ++ atoms_context G)) as [x Hx].
      apply lc_tm_open_rec_inv with (u:=tm_fvar x).
      apply IHbody.
      intro Hin; apply Hx; apply in_or_app; left; exact Hin.
  - intros D G t1 t2 T1 T2 H1 IH1 H2 IH2.
    constructor; assumption.
  - intros L D G t0 T0 Hbody IHbody.
    apply lc_tm_tabs.
    destruct (fresh_atom L) as [X HX].
    apply lc_tm_ty_open_rec_inv with (U:=Ty_FVar X).
    apply IHbody.
    exact HX.
  - intros D G t0 T0 U Ht IHt Hwf.
    constructor.
    + exact IHt.
    + eapply wf_ty_lc; eassumption.
  - intros D G t1 t2 T0 H1 IH1 H2 IH2.
    constructor; assumption.
Qed.

Definition ty_update (phi : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb X Y then U else phi Y.

Definition tm_update (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb x y then u else sigma y.

Fixpoint tm_vars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => tm_vars t1
  | tm_app t1 t2 => tm_vars t1 ++ tm_vars t2
  | tm_tabs t1 => tm_vars t1
  | tm_tapp t1 _ => tm_vars t1
  | tm_choice t1 t2 => tm_vars t1 ++ tm_vars t2
  end.

Lemma tm_vars_atoms : forall t x, In x (tm_vars t) -> In x (atoms_tm t).
Proof.
  induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH T|t1 IH1 t2 IH2];
    simpl; intros x H.
  - contradiction.
  - simpl in H; destruct H as [->|[]]. simpl; auto.
  - apply in_or_app; right; apply IH; exact H.
  - apply in_or_app. apply in_app_or in H. destruct H as [H|H].
    + left; apply IH1; exact H.
    + right; apply IH2; exact H.
  - apply IH; exact H.
  - apply in_or_app; left; apply IH; exact H.
  - apply in_or_app. apply in_app_or in H. destruct H as [H|H].
    + left; apply IH1; exact H.
    + right; apply IH2; exact H.
Qed.

Lemma open_ty_rec_closed : forall K k U T,
    lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  intros K k U T H Hle. revert K k U H Hle.
  induction T as [i|X|T1 IH1 T2 IH2|T IH];
    intros K k U H Hle; simpl in *.
  - inversion H; destruct (Nat.eqb_spec k i) as [Heq|Hne]; [lia|reflexivity].
  - reflexivity.
  - inversion H; simpl; f_equal; [eapply IH1|eapply IH2]; eauto.
  - inversion H; simpl; f_equal; eapply IH; eauto; lia.
Qed.

Lemma open_tm_rec_closed : forall K j k u t,
    lc_tm_at K j t -> j <= k -> open_tm_rec k u t = t.
Proof.
  intros K j k u t H Hle. revert K j k u H Hle.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH|t1 IH1 t2 IH2];
    intros K j k u H Hle; simpl in *.
  - inversion H; destruct (Nat.eqb_spec k i) as [Heq|Hne]; [lia|reflexivity].
  - reflexivity.
  - inversion H; f_equal; eapply IH; eauto; lia.
  - inversion H; f_equal; eauto.
  - inversion H; f_equal; eapply IH; eauto.
  - inversion H; f_equal; eauto.
  - inversion H; f_equal; eauto.
Qed.

Lemma ty_fsubst_update_open_rec : forall k T X U phi,
    ~ In X (atoms_ty T) ->
    (forall Y, locally_closed_ty (phi Y)) ->
    ty_fsubst (ty_update phi X U) (open_ty_rec k (Ty_FVar X) T) =
    open_ty_rec k U (ty_fsubst phi T).
Proof.
  intros k T. revert k.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH];
    intros k X U phi Hfresh Hphi; unfold ty_update; simpl.
  - destruct (Nat.eqb_spec k i) as [->|Hne].
    + destruct (Nat.eqb X X) eqn:E.
      * cbn [ty_fsubst]. rewrite E. reflexivity.
      * exfalso. apply (Nat.eqb_neq X X) in E. apply E. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb_spec X Y) as [->|Hne].
    + exfalso. apply Hfresh. simpl; auto.
    + cbn [ty_fsubst]. rewrite (open_ty_rec_closed 0 k U (phi Y)); [reflexivity|apply Hphi|lia].
  - assert (HF1 : ~ In X (atoms_ty T1)).
    { intro H; apply Hfresh; apply in_or_app; left; exact H. }
    assert (HF2 : ~ In X (atoms_ty T2)).
    { intro H; apply Hfresh; apply in_or_app; right; exact H. }
    f_equal.
    + apply (IH1 k X U phi HF1 Hphi).
    + apply (IH2 k X U phi HF2 Hphi).
  - assert (HF : ~ In X (atoms_ty T)).
    { intro H; apply Hfresh; exact H. }
    f_equal. apply (IH (S k) X U phi HF Hphi).
Qed.

Lemma tm_fsubst_update_open_ty_rec : forall k t X U phi,
    ~ In X (atoms_tm t) ->
    (forall Y, locally_closed_ty (phi Y)) ->
    tm_fsubst (ty_update phi X U) (open_tm_ty_rec k (Ty_FVar X) t) =
    open_tm_ty_rec k U (tm_fsubst phi t).
Proof.
  intros k t; revert k.
  induction t as
    [i|y|T t IHt|t1 IH1 t2 IH2|t IH|t IH T|t1 IH1 t2 IH2];
    intros k X U phi Hfresh Hphi; simpl.
  - reflexivity.
  - reflexivity.
  - assert (HFt : ~ In X (atoms_tm t)).
    { intro H; apply Hfresh; apply in_or_app; right; exact H. }
    assert (HFT : ~ In X (atoms_ty T)).
    { intro H; apply Hfresh; apply in_or_app; left; exact H. }
    f_equal.
    + apply (ty_fsubst_update_open_rec k T X U phi HFT Hphi).
    + apply (IHt k X U phi HFt Hphi).
  - assert (HF1 : ~ In X (atoms_tm t1)).
    { intro H; apply Hfresh; apply in_or_app; left; exact H. }
    assert (HF2 : ~ In X (atoms_tm t2)).
    { intro H; apply Hfresh; apply in_or_app; right; exact H. }
    f_equal; [apply (IH1 k X U phi HF1 Hphi)|apply (IH2 k X U phi HF2 Hphi)].
  - assert (HF : ~ In X (atoms_tm t)).
    { intro H; apply Hfresh; exact H. }
    f_equal. apply (IH (S k) X U phi HF Hphi).
  - assert (HFt : ~ In X (atoms_tm t)).
    { intro H; apply Hfresh; apply in_or_app; left; exact H. }
    assert (HFT : ~ In X (atoms_ty T)).
    { intro H; apply Hfresh; apply in_or_app; right; exact H. }
    f_equal.
    + apply (IH k X U phi HFt Hphi).
    + apply (ty_fsubst_update_open_rec k T X U phi HFT Hphi).
  - assert (HF1 : ~ In X (atoms_tm t1)).
    { intro H; apply Hfresh; apply in_or_app; left; exact H. }
    assert (HF2 : ~ In X (atoms_tm t2)).
    { intro H; apply Hfresh; apply in_or_app; right; exact H. }
    f_equal; [apply (IH1 k X U phi HF1 Hphi)|apply (IH2 k X U phi HF2 Hphi)].
Qed.

Lemma tm_fvar_subst_update_open_rec : forall k t x u sigma,
    ~ In x (tm_vars t) ->
    (forall y, locally_closed_tm (sigma y)) ->
    tm_fvar_subst (tm_update sigma x u) (open_tm_rec k (tm_fvar x) t) =
    open_tm_rec k u (tm_fvar_subst sigma t).
Proof.
  intros k t; revert k.
  induction t as
    [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH|t1 IH1 t2 IH2];
    intros k x u sigma Hfresh Hsigma; unfold tm_update; simpl.
  - destruct (Nat.eqb_spec k i) as [->|Hne].
    + destruct (Nat.eqb x x) eqn:E.
      * cbn [tm_fvar_subst]; rewrite E; reflexivity.
      * exfalso. apply (Nat.eqb_neq x x) in E. apply E. reflexivity.
    + reflexivity.
  - destruct (Nat.eqb_spec x y) as [->|Hne].
    + exfalso. apply Hfresh. simpl; auto.
    + cbn [tm_fvar_subst].
      rewrite (open_tm_rec_closed 0 0 k u (sigma y)); [reflexivity|apply Hsigma|lia].
  - assert (HF : ~ In x (tm_vars t)).
    { intro H; apply Hfresh; exact H. }
    f_equal. apply (IH (S k) x u sigma HF Hsigma).
  - assert (HF1 : ~ In x (tm_vars t1)).
    { intro H; apply Hfresh; apply in_or_app; left; exact H. }
    assert (HF2 : ~ In x (tm_vars t2)).
    { intro H; apply Hfresh; apply in_or_app; right; exact H. }
    f_equal; [apply (IH1 k x u sigma HF1 Hsigma)|apply (IH2 k x u sigma HF2 Hsigma)].
  - assert (HF : ~ In x (tm_vars t)).
    { intro H; apply Hfresh; exact H. }
    f_equal. apply (IH k x u sigma HF Hsigma).
  - assert (HF : ~ In x (tm_vars t)).
    { intro H; apply Hfresh; exact H. }
    f_equal. apply (IH k x u sigma HF Hsigma).
  - assert (HF1 : ~ In x (tm_vars t1)).
    { intro H; apply Hfresh; apply in_or_app; left; exact H. }
    assert (HF2 : ~ In x (tm_vars t2)).
    { intro H; apply Hfresh; apply in_or_app; right; exact H. }
    f_equal; [apply (IH1 k x u sigma HF1 Hsigma)|apply (IH2 k x u sigma HF2 Hsigma)].
Qed.

Lemma tm_fsubst_open_tm_rec : forall k phi z t,
    tm_fsubst phi (open_tm_rec k (tm_fvar z) t) =
    open_tm_rec k (tm_fvar z) (tm_fsubst phi t).
Proof.
  intros k phi z t. revert k.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH|t1 IH1 t2 IH2];
    intros k; simpl.
  - destruct (Nat.eqb_spec k i); reflexivity.
  - reflexivity.
  - f_equal. apply IH.
  - f_equal; [apply IH1|apply IH2].
  - f_equal. apply IH.
  - f_equal. apply IH.
  - f_equal; [apply IH1|apply IH2].
Qed.

Lemma tm_vars_fsubst : forall phi t, tm_vars (tm_fsubst phi t) = tm_vars t.
Proof.
  intros phi t; induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2; reflexivity.
Qed.

Lemma tm_inst_update_open_tm : forall t x u phi sigma,
    ~ In x (atoms_tm t) ->
    (forall y, locally_closed_tm (sigma y)) ->
    tm_inst phi (tm_update sigma x u) (open_tm t (tm_fvar x)) =
    open_tm (tm_inst phi sigma t) u.
Proof.
  intros t x u phi sigma H Hsigma.
  unfold tm_inst, open_tm.
  rewrite (tm_fsubst_open_tm_rec 0 phi x t).
  rewrite tm_fvar_subst_update_open_rec; [reflexivity| |exact Hsigma].
  rewrite tm_vars_fsubst. intro Hv; apply H; apply tm_vars_atoms; exact Hv.
Qed.

Lemma open_tm_ty_rec_closed : forall K j k U t,
    lc_tm_at K j t -> K <= k -> open_tm_ty_rec k U t = t.
Proof.
  intros K j k U t H Hle. revert K j k U H Hle.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH|t1 IH1 t2 IH2];
    intros K j k U H Hle; simpl in *.
  - reflexivity.
  - reflexivity.
  - inversion H; f_equal; eauto using open_ty_rec_closed, IH; lia.
  - inversion H; f_equal; [eapply IH1|eapply IH2]; eauto.
  - inversion H; f_equal; eapply IH; eauto; lia.
  - inversion H; f_equal; [eapply IH|eapply open_ty_rec_closed]; eauto; lia.
  - inversion H; f_equal; [eapply IH1|eapply IH2]; eauto.
Qed.

Lemma tm_fvar_subst_open_tm_ty_rec : forall k sigma U t,
    (forall x, locally_closed_tm (sigma x)) ->
    tm_fvar_subst sigma (open_tm_ty_rec k U t) =
    open_tm_ty_rec k U (tm_fvar_subst sigma t).
Proof.
  intros k sigma U t Hsigma. revert k.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH|t1 IH1 t2 IH2];
    intros k; simpl.
  - reflexivity.
  - rewrite (open_tm_ty_rec_closed 0 0 k U (sigma x)); [reflexivity|apply Hsigma|lia].
  - f_equal. apply IH.
  - f_equal; [apply IH1|apply IH2].
  - f_equal. apply IH.
  - f_equal. apply IH.
  - f_equal; [apply IH1|apply IH2].
Qed.

Lemma tm_inst_update_open_ty : forall t X U phi sigma,
    ~ In X (atoms_tm t) ->
    (forall Y, locally_closed_ty (phi Y)) ->
    (forall y, locally_closed_tm (sigma y)) ->
    tm_inst (ty_update phi X U) sigma
      (open_tm_ty t (Ty_FVar X)) =
    open_tm_ty (tm_inst phi sigma t) U.
Proof.
  intros t X U phi sigma H Hphi Hsigma.
  unfold tm_inst, open_tm_ty.
  rewrite tm_fsubst_update_open_ty_rec; [|exact H|exact Hphi].
  rewrite (tm_fvar_subst_open_tm_ty_rec 0 sigma U (tm_fsubst phi t) Hsigma).
  reflexivity.
Qed.



Theorem fundamental_theorem : fundamental_statement_lc.
Proof.
  unfold fundamental_statement_lc.
  intros Delta Gamma t T HT HLC.
  refine (has_type_ind
    (fun D G q S => locally_closed_tm q ->
      forall eta rho phi1 phi2 sigma1 sigma2,
        type_env_related eta rho D ->
        (forall X, locally_closed_ty (phi1 X)) ->
        (forall X, locally_closed_ty (phi2 X)) ->
        (forall x, locally_closed_tm (sigma1 x)) ->
        (forall x, locally_closed_tm (sigma2 x)) ->
        term_env_related eta rho G sigma1 sigma2 ->
        expression_relation eta rho S
          (tm_inst phi1 sigma1 q) (tm_inst phi2 sigma2 q))
    _ _ _ _ _ _ Delta Gamma t T HT HLC).
  - intros D G x T0 Hlookup Hwf Hlc0 eta rho phi1 phi2 sigma1 sigma2
      Henv Hphi1 Hphi2 Hsig1 Hsig2 Hterm.
    unfold expression_relation, expression_lifting, results_match.
    split; [apply Hsig1|]. split; [apply Hsig2|].
    pose proof (vr_values_wf D T0 eta rho (sigma1 x) (sigma2 x)
      Hwf Henv (Hterm x T0 Hlookup)) as [V1 V2].
    exists (sigma1 x), (sigma2 x).
    split; [constructor; exact V1|]. split; [constructor; exact V2|].
    exact (Hterm x T0 Hlookup).
  - intros L D G T1 t2 T2 Hwf Hbody IHbody Hlc0 eta rho phi1 phi2 sigma1 sigma2
      Henv Hphi1 Hphi2 Hsig1 Hsig2 Hterm.
    unfold expression_relation, expression_lifting, results_match.
    split; [apply (lc_tm_inst _ phi1 sigma1 Hlc0 Hphi1 Hsig1)|].
    split; [apply (lc_tm_inst _ phi2 sigma2 Hlc0 Hphi2 Hsig2)|].
    exists (tm_abs (ty_fsubst phi1 T1) (tm_fvar_subst sigma1 (tm_fsubst phi1 t2))),
      (tm_abs (ty_fsubst phi2 T1) (tm_fvar_subst sigma2 (tm_fsubst phi2 t2))).
    split; [apply EvalValue; apply v_abs; apply (lc_tm_inst _ phi1 sigma1 Hlc0 Hphi1 Hsig1)|].
    split; [apply EvalValue; apply v_abs; apply (lc_tm_inst _ phi2 sigma2 Hlc0 Hphi2 Hsig2)|].
    split; [apply v_abs; apply (lc_tm_inst _ phi1 sigma1 Hlc0 Hphi1 Hsig1)|].
    split; [apply v_abs; apply (lc_tm_inst _ phi2 sigma2 Hlc0 Hphi2 Hsig2)|].
    exists (ty_fsubst phi1 T1), (tm_fvar_subst sigma1 (tm_fsubst phi1 t2)),
      (ty_fsubst phi2 T1), (tm_fvar_subst sigma2 (tm_fsubst phi2 t2)).
    split; [reflexivity|]. split; [reflexivity|].
    intros arg1 arg2 Harg.
    destruct (fresh_atom (L ++ atoms_tm t2 ++ atoms_context G)) as [x Hx].
    assert (HnotL : ~ In x L) by (intro h; apply Hx; apply in_or_app; left; exact h).
    assert (Ht2fresh : ~ In x (atoms_tm t2)) by
      (intro h; apply Hx; apply in_or_app; right; apply in_or_app; left; exact h).
    assert (HGfresh : ~ In x (atoms_context G)) by
      (intro h; apply Hx; apply in_or_app; right; apply in_or_app; right; exact h).
    pose proof (vr_values_wf D T1 eta rho arg1 arg2 Hwf Henv Harg) as [Varg1 Varg2].
    assert (S1 : forall y, locally_closed_tm (tm_update sigma1 x arg1 y)).
    { intro y; unfold tm_update; destruct (Nat.eqb_spec x y); subst; eauto using value_lc. }
    assert (S2 : forall y, locally_closed_tm (tm_update sigma2 x arg2 y)).
    { intro y; unfold tm_update; destruct (Nat.eqb_spec x y); subst; eauto using value_lc. }
    assert (TE : term_env_related eta rho (update G x T1)
        (tm_update sigma1 x arg1) (tm_update sigma2 x arg2)).
    { intros y S Hy. unfold tm_update.
      destruct (Nat.eqb_spec x y) as [->|Hxy].
      - simpl in Hy. destruct (Nat.eqb y y) eqn:E.
        + inversion Hy; inversion H0; rewrite <- H0; exact Harg.
        + exfalso. apply (Nat.eqb_neq y y) in E. apply E. reflexivity.
      - apply Hterm. simpl in Hy.
        destruct (Nat.eqb y x) eqn:E.
        + exfalso. apply Hxy. symmetry; apply Nat.eqb_eq; exact E.
        + exact Hy. }
    assert (BLC : locally_closed_tm (open_tm t2 (tm_fvar x))).
    { unfold locally_closed_tm; apply lc_tm_open_rec with (K:=0) (k:=0).
      - inversion Hlc0; assumption.
      - constructor. }
    pose proof (IHbody x HnotL BLC eta rho phi1 phi2
      (tm_update sigma1 x arg1) (tm_update sigma2 x arg2)
      Henv Hphi1 Hphi2 S1 S2 TE) as E.
    rewrite (tm_inst_update_open_tm t2 x arg1 phi1 sigma1 Ht2fresh Hsig1) in E.
    rewrite (tm_inst_update_open_tm t2 x arg2 phi2 sigma2 Ht2fresh Hsig2) in E.
    exact E.
  - intros D G t1 t2 T1 T2 Hf IHf Ha IHa Hlc0 eta rho phi1 phi2 sigma1 sigma2
      Henv Hphi1 Hphi2 Hsig1 Hsig2 Hterm.
    unfold expression_relation, expression_lifting, results_match in *.
    pose proof (IHf Hlc0 eta rho phi1 phi2 sigma1 sigma2
      Henv Hphi1 Hphi2 Hsig1 Hsig2 Hterm) as Ef.
    pose proof (IHa Hlc0 eta rho phi1 phi2 sigma1 sigma2
      Henv Hphi1 Hphi2 Hsig1 Hsig2 Hterm) as Ea.
    destruct Ef as [LCf1 [LCf2 [af1 [af2 [Eaf1 [Eaf2 Raf]]]]]].
    destruct Ea as [LCa1 [LCa2 [av1 [av2 [Eav1 [Eav2 Rav]]]]]].
    destruct Raf as [Vf1 [Vf2 [U1 [b1 [U2 [b2 [F1 [F2 Rfun]]]]]]]].
    destruct Rav as [Vav1 [Vav2 [r1 [r2 [Ar1 [Ar2 Rarg]]]]]].
    destruct (Rfun av1 av2 Rav) as [LCb1 [LCb2 [z1 [z2 [Eb1 [Eb2 Rbody]]]]]].
    unfold expression_relation, expression_lifting, results_match.
    split; [apply lc_tm_inst; exact Hlc0|].
    split; [apply lc_tm_inst; exact Hlc0|].
    exists z1, z2.
    split; [eapply EvalApp; eauto|]. split; [eapply EvalApp; eauto|].
    exact Rbody.
  - admit.
  - admit.
  - admit.
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
Abort.

End SystemFParametricityNondeterminismMediumTask.
