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
(* Auxiliary infrastructure for the parametricity proof.        *)
(* ============================================================ *)

(* ---------- fresh atoms ---------- *)

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (max_list l')
  end.

Definition fresh (l : list nat) : nat := S (max_list l).

Lemma max_list_ge : forall l x, In x l -> x <= max_list l.
Proof.
  induction l as [| y l IH]; intros x Hin.
  - destruct Hin.
  - simpl in *. destruct Hin as [<- | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans.
      * apply IH; exact Hin.
      * apply Nat.le_max_r.
Qed.

Lemma fresh_not_in : forall l, ~ In (fresh l) l.
Proof.
  intros l Hin. unfold fresh in Hin.
  pose proof (max_list_ge l (S (max_list l)) Hin). lia.
Qed.

(* ---------- free atoms of types, terms and contexts ---------- *)

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T1 => fv_ty T1
  end.

Fixpoint fv_tm_ty (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T t1 => fv_ty T ++ fv_tm_ty t1
  | tm_app t1 t2 => fv_tm_ty t1 ++ fv_tm_ty t2
  | tm_tabs t1 => fv_tm_ty t1
  | tm_tapp t1 T => fv_tm_ty t1 ++ fv_ty T
  | tm_choice t1 t2 => fv_tm_ty t1 ++ fv_tm_ty t2
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => fv_tm t1
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs t1 => fv_tm t1
  | tm_tapp t1 _ => fv_tm t1
  | tm_choice t1 t2 => fv_tm t1 ++ fv_tm t2
  end.

Fixpoint fv_ctx (G : context) : list atom :=
  match G with
  | [] => []
  | (x, T) :: G' => x :: fv_ty T ++ fv_ctx G'
  end.

(* ---------- locally closed types: basic lemmas ---------- *)

Lemma lc_ty_at_mono : forall T k k',
  k <= k' -> lc_ty_at k T -> lc_ty_at k' T.
Proof.
  induction T; intros k k' Hle H; inversion H; subst.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow.
    + apply IHT1 with (k := k); [assumption | assumption].
    + apply IHT2 with (k := k); [assumption | assumption].
  - apply lc_ty_all. apply IHT with (k := S k); [lia | assumption].
Qed.

(* Substituting a type U for the bound variable at depth k of T. *)
Lemma lc_ty_at_open : forall T k U,
  lc_ty_at (S k) T ->
  lc_ty_at k U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U Hlc HU; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply HU.
    + apply Nat.eqb_neq in E.
      inversion Hlc; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion Hlc; subst.
    apply lc_ty_arrow.
    + apply IHT1 with (k := k) (U := U); assumption.
    + apply IHT2 with (k := k) (U := U); assumption.
  - inversion Hlc; subst.
    apply lc_ty_all.
    apply IHT with (k := S k) (U := U).
    + assumption.
    + apply lc_ty_at_mono with (k := k); [lia | exact HU].
Qed.

Lemma lc_ty_at_open_inv : forall T k U,
  lc_ty_at k (open_ty_rec k U T) ->
  lc_ty_at (S k) T.
Proof.
  induction T; intros k U H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_ty_bvar. lia.
    + apply Nat.eqb_neq in E.
      inversion H; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion H; subst.
    apply lc_ty_arrow.
    + apply IHT1 with (k := k) (U := U); assumption.
    + apply IHT2 with (k := k) (U := U); assumption.
  - inversion H; subst.
    apply lc_ty_all.
    apply IHT with (k := S k) (U := U). assumption.
Qed.

(* More general inverse direction: opening with an arbitrary U. *)
Lemma lc_ty_at_open_inv_gen : forall T j K U,
  j <= K ->
  lc_ty_at K (open_ty_rec j U T) ->
  lc_ty_at (S K) T.
Proof.
  induction T; intros j K U Hle H; simpl in H.
  - destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_ty_bvar. lia.
    + apply Nat.eqb_neq in E.
      inversion H; subst. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - inversion H; subst.
    apply lc_ty_arrow.
    + apply IHT1 with (j := j) (K := K) (U := U); [assumption | assumption].
    + apply IHT2 with (j := j) (K := K) (U := U); [assumption | assumption].
  - inversion H; subst.
    apply lc_ty_all.
    apply IHT with (j := S j) (K := S K) (U := U); [lia | assumption].
Qed.

(* Well-formed types are locally closed. *)
Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    pose proof (H0 (fresh L) (fresh_not_in L)) as Hwf.
    apply (lc_ty_at_open_inv_gen T 0 0 (Ty_FVar (fresh L))); [lia | exact Hwf].
Qed.

(* ---------- locally closed terms: basic lemmas ---------- *)

Lemma lc_tm_at_mono : forall t K K' k k',
  K <= K' -> k <= k' -> lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
  intros K K' k k' HK Hk H; inversion H; subst.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_at_mono with (k := K); assumption.
    + apply IH1 with (K := K) (k := S k); [assumption | lia | assumption].
  - apply lc_tm_app.
    + apply IH1 with (K := K) (k := k); assumption.
    + apply IH2 with (K := K) (k := k); assumption.
  - apply lc_tm_tabs.
    apply IH1 with (K := S K) (k := k); [lia | assumption | assumption].
  - apply lc_tm_tapp.
    + apply IH1 with (K := K) (k := k); assumption.
    + apply lc_ty_at_mono with (k := K); assumption.
  - apply lc_tm_choice.
    + apply IH1 with (K := K) (k := k); assumption.
    + apply IH2 with (K := K) (k := k); assumption.
Qed.

(* Inverse of term-variable opening. *)
Lemma lc_tm_at_open_tm_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t as [n | y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
  intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst n. apply lc_tm_bvar. lia.
    + apply Nat.eqb_neq in E. inversion H; subst. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + assumption.
    + apply IH1 with (K := K) (k := S k) (x := x). assumption.
  - inversion H; subst. apply lc_tm_app.
    + apply IH1 with (K := K) (k := k) (x := x). assumption.
    + apply IH2 with (K := K) (k := k) (x := x). assumption.
  - inversion H; subst. apply lc_tm_tabs.
    apply IH1 with (K := S K) (k := k) (x := x). assumption.
  - inversion H; subst. apply lc_tm_tapp.
    + apply IH1 with (K := K) (k := k) (x := x). assumption.
    + assumption.
  - inversion H; subst. apply lc_tm_choice.
    + apply IH1 with (K := K) (k := k) (x := x). assumption.
    + apply IH2 with (K := K) (k := k) (x := x). assumption.
Qed.

(* Inverse of type-variable opening in terms. *)
Lemma lc_tm_at_open_tm_ty_inv : forall t j K k U,
  j <= K ->
  lc_tm_at K k (open_tm_ty_rec j U t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t as [n | y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
  intros j K k U Hle H; simpl in H.
  - inversion H; subst. apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - inversion H; subst. apply lc_tm_abs.
    + apply (lc_ty_at_open_inv_gen T j K U Hle). assumption.
    + apply IH1 with (j := j) (K := K) (k := S k) (U := U); assumption.
  - inversion H; subst. apply lc_tm_app.
    + apply IH1 with (j := j) (K := K) (k := k) (U := U); assumption.
    + apply IH2 with (j := j) (K := K) (k := k) (U := U); assumption.
  - inversion H; subst. apply lc_tm_tabs.
    apply IH1 with (j := S j) (K := S K) (k := k) (U := U); [lia | assumption].
  - inversion H; subst. apply lc_tm_tapp.
    + apply IH1 with (j := j) (K := K) (k := k) (U := U); assumption.
    + apply (lc_ty_at_open_inv_gen T j K U Hle). assumption.
  - inversion H; subst. apply lc_tm_choice.
    + apply IH1 with (j := j) (K := K) (k := k) (U := U); assumption.
    + apply IH2 with (j := j) (K := K) (k := k) (U := U); assumption.
Qed.

(* ---------- simultaneous substitutions ---------- *)

Fixpoint ty_subst_all (sigma : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sigma X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst_all sigma T1) (ty_subst_all sigma T2)
  | Ty_All T1 => Ty_All (ty_subst_all sigma T1)
  end.

Fixpoint tm_ty_subst_all (sigma : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_subst_all sigma T) (tm_ty_subst_all sigma t1)
  | tm_app t1 t2 => tm_app (tm_ty_subst_all sigma t1) (tm_ty_subst_all sigma t2)
  | tm_tabs t1 => tm_tabs (tm_ty_subst_all sigma t1)
  | tm_tapp t1 T => tm_tapp (tm_ty_subst_all sigma t1) (ty_subst_all sigma T)
  | tm_choice t1 t2 => tm_choice (tm_ty_subst_all sigma t1) (tm_ty_subst_all sigma t2)
  end.

Fixpoint tm_subst_all (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs T (tm_subst_all sigma t1)
  | tm_app t1 t2 => tm_app (tm_subst_all sigma t1) (tm_subst_all sigma t2)
  | tm_tabs t1 => tm_tabs (tm_subst_all sigma t1)
  | tm_tapp t1 T => tm_tapp (tm_subst_all sigma t1) T
  | tm_choice t1 t2 => tm_choice (tm_subst_all sigma t1) (tm_subst_all sigma t2)
  end.

Fixpoint subst_all (sigma_ty : atom -> ty) (sigma_tm : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma_tm x
  | tm_abs T t1 => tm_abs (ty_subst_all sigma_ty T) (subst_all sigma_ty sigma_tm t1)
  | tm_app t1 t2 => tm_app (subst_all sigma_ty sigma_tm t1) (subst_all sigma_ty sigma_tm t2)
  | tm_tabs t1 => tm_tabs (subst_all sigma_ty sigma_tm t1)
  | tm_tapp t1 T => tm_tapp (subst_all sigma_ty sigma_tm t1) (ty_subst_all sigma_ty T)
  | tm_choice t1 t2 => tm_choice (subst_all sigma_ty sigma_tm t1) (subst_all sigma_ty sigma_tm t2)
  end.

(* ---------- local closure is preserved by substitution ---------- *)

Lemma lc_ty_at_ty_subst_all : forall T sigma K,
  lc_ty_at K T ->
  (forall X, lc_ty_at 0 (sigma X)) ->
  lc_ty_at K (ty_subst_all sigma T).
Proof.
  induction T; intros sigma K Hlc Hsig; simpl.
  - inversion Hlc; subst. apply lc_ty_bvar. assumption.
  - apply lc_ty_at_mono with (k := 0); [lia | apply Hsig].
  - inversion Hlc; subst. apply lc_ty_arrow.
    + apply IHT1; assumption.
    + apply IHT2; assumption.
  - inversion Hlc; subst. apply lc_ty_all.
    apply IHT; assumption.
Qed.

Lemma lc_tm_at_tm_ty_subst_all : forall t sigma K k,
  lc_tm_at K k t ->
  (forall X, lc_ty_at 0 (sigma X)) ->
  lc_tm_at K k (tm_ty_subst_all sigma t).
Proof.
  induction t; intros sigma K k Hlc Hsig; simpl.
  - assumption.
  - assumption.
  - inversion Hlc; subst. apply lc_tm_abs.
    + apply lc_ty_at_ty_subst_all; assumption.
    + apply IHt; assumption.
  - inversion Hlc; subst. apply lc_tm_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - inversion Hlc; subst. apply lc_tm_tabs.
    apply IHt; assumption.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + apply IHt; assumption.
    + apply lc_ty_at_ty_subst_all; assumption.
  - inversion Hlc; subst. apply lc_tm_choice.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
Qed.

Lemma lc_tm_at_tm_subst_all : forall t sigma K k,
  lc_tm_at K k t ->
  (forall x, lc_tm_at 0 0 (sigma x)) ->
  lc_tm_at K k (tm_subst_all sigma t).
Proof.
  induction t; intros sigma K k Hlc Hsig; simpl.
  - assumption.
  - apply lc_tm_at_mono with (K := 0) (k := 0); [lia | lia | apply Hsig].
  - inversion Hlc; subst. apply lc_tm_abs.
    + assumption.
    + apply IHt; assumption.
  - inversion Hlc; subst. apply lc_tm_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - inversion Hlc; subst. apply lc_tm_tabs.
    apply IHt; assumption.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + apply IHt; assumption.
    + assumption.
  - inversion Hlc; subst. apply lc_tm_choice.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
Qed.

Lemma lc_tm_at_subst_all : forall t sigma_ty sigma_tm K k,
  lc_tm_at K k t ->
  (forall X, lc_ty_at 0 (sigma_ty X)) ->
  (forall x, lc_tm_at 0 0 (sigma_tm x)) ->
  lc_tm_at K k (subst_all sigma_ty sigma_tm t).
Proof.
  induction t; intros sigma_ty sigma_tm K k Hlc Hsty Hstm; simpl.
  - assumption.
  - apply lc_tm_at_mono with (K := 0) (k := 0); [lia | lia | apply Hstm].
  - inversion Hlc; subst. apply lc_tm_abs.
    + apply lc_ty_at_ty_subst_all; assumption.
    + apply IHt; assumption.
  - inversion Hlc; subst. apply lc_tm_app.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - inversion Hlc; subst. apply lc_tm_tabs.
    apply IHt; assumption.
  - inversion Hlc; subst. apply lc_tm_tapp.
    + apply IHt; assumption.
    + apply lc_ty_at_ty_subst_all; assumption.
  - inversion Hlc; subst. apply lc_tm_choice.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
Qed.

(* ---------- substitution extensionality ---------- *)

Lemma ty_subst_all_ext : forall T sigma1 sigma2,
  (forall X, In X (fv_ty T) -> sigma1 X = sigma2 X) ->
  ty_subst_all sigma1 T = ty_subst_all sigma2 T.
Proof.
  induction T; intros sigma1 sigma2 H; simpl.
  - reflexivity.
  - apply H. simpl. left. reflexivity.
  - f_equal.
    + apply IHT1. intros X Hin. apply H. simpl. apply in_or_app. left. assumption.
    + apply IHT2. intros X Hin. apply H. simpl. apply in_or_app. right. assumption.
  - f_equal. apply IHT. intros X Hin. apply H. simpl. assumption.
Qed.

Lemma subst_all_ext : forall t sigma_ty1 sigma_ty2 sigma_tm1 sigma_tm2,
  (forall X, In X (fv_tm_ty t) -> sigma_ty1 X = sigma_ty2 X) ->
  (forall x, In x (fv_tm t) -> sigma_tm1 x = sigma_tm2 x) ->
  subst_all sigma_ty1 sigma_tm1 t = subst_all sigma_ty2 sigma_tm2 t.
Proof.
  induction t as [n | y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
  intros sty1 sty2 stm1 stm2 Hty Htm; simpl.
  - reflexivity.
  - apply Htm. simpl. left. reflexivity.
  - f_equal.
    + apply ty_subst_all_ext. intros X Hin. apply Hty.
      simpl. apply in_or_app. left. assumption.
    + apply IH1.
      * intros X Hin. apply Hty. simpl. apply in_or_app. right. assumption.
      * intros x Hin. apply Htm. simpl. assumption.
  - f_equal.
    + apply IH1.
      * intros X Hin. apply Hty. simpl. apply in_or_app. left. assumption.
      * intros x Hin. apply Htm. simpl. apply in_or_app. left. assumption.
    + apply IH2.
      * intros X Hin. apply Hty. simpl. apply in_or_app. right. assumption.
      * intros x Hin. apply Htm. simpl. apply in_or_app. right. assumption.
  - f_equal. apply IH1.
    * intros X Hin. apply Hty. simpl. assumption.
    * intros x Hin. apply Htm. simpl. assumption.
  - f_equal.
    + apply IH1.
      * intros X Hin. apply Hty. simpl. apply in_or_app. left. assumption.
      * intros x Hin. apply Htm. simpl. assumption.
    + apply ty_subst_all_ext. intros X Hin. apply Hty.
      simpl. apply in_or_app. right. assumption.
  - f_equal.
    + apply IH1.
      * intros X Hin. apply Hty. simpl. apply in_or_app. left. assumption.
      * intros x Hin. apply Htm. simpl. apply in_or_app. left. assumption.
    + apply IH2.
      * intros X Hin. apply Hty. simpl. apply in_or_app. right. assumption.
      * intros x Hin. apply Htm. simpl. apply in_or_app. right. assumption.
Qed.

(* ---------- opening of locally closed objects is the identity ---------- *)

Lemma open_ty_rec_lc_id : forall T n j U,
  lc_ty_at n T -> n <= j -> open_ty_rec j U T = T.
Proof.
  induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1];
  intros n j U Hlc Hle; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + apply IH1 with (n := n); assumption.
    + apply IH2 with (n := n); assumption.
  - inversion Hlc; subst. f_equal.
    apply IH1 with (n := S n); [assumption | lia].
Qed.

Lemma open_tm_rec_lc_id : forall t K k j u,
  lc_tm_at K k t -> k <= j -> open_tm_rec j u t = t.
Proof.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
  intros K k j u Hlc Hle; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    apply IH1 with (K := K) (k := S k); [assumption | lia].
  - inversion Hlc; subst. f_equal.
    + apply IH1 with (K := K) (k := k); assumption.
    + apply IH2 with (K := K) (k := k); assumption.
  - inversion Hlc; subst. f_equal.
    apply IH1 with (K := S K) (k := k); assumption.
  - inversion Hlc; subst. f_equal.
    apply IH1 with (K := K) (k := k); assumption.
  - inversion Hlc; subst. f_equal.
    + apply IH1 with (K := K) (k := k); assumption.
    + apply IH2 with (K := K) (k := k); assumption.
Qed.

Lemma open_tm_ty_rec_lc_id : forall t K k j U,
  lc_tm_at K k t -> K <= j -> open_tm_ty_rec j U t = t.
Proof.
  induction t as [n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
  intros K k j U Hlc Hle; simpl.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + apply open_ty_rec_lc_id with (n := K); assumption.
    + apply IH1 with (K := K) (k := S k); [assumption | assumption].
  - inversion Hlc; subst. f_equal.
    + apply IH1 with (K := K) (k := k); assumption.
    + apply IH2 with (K := K) (k := k); assumption.
  - inversion Hlc; subst. f_equal.
    apply IH1 with (K := S K) (k := k); [assumption | lia].
  - inversion Hlc; subst. f_equal.
    + apply IH1 with (K := K) (k := k); assumption.
    + apply open_ty_rec_lc_id with (n := K); assumption.
  - inversion Hlc; subst. f_equal.
    + apply IH1 with (K := K) (k := k); assumption.
    + apply IH2 with (K := K) (k := k); assumption.
Qed.

(* ---------- substitution / opening commutation ---------- *)

Lemma ty_subst_all_open_ty_rec : forall T sigma j X,
  (forall Y, lc_ty_at 0 (sigma Y)) ->
  ty_subst_all sigma (open_ty_rec j (Ty_FVar X) T) =
  open_ty_rec j (sigma X) (ty_subst_all sigma T).
Proof.
  induction T as [i | Y | T1 IH1 T2 IH2 | T1 IH1];
  intros sigma j X Hsig; simpl.
  - destruct (Nat.eqb j i); reflexivity.
  - rewrite open_ty_rec_lc_id with (n := 0) (j := j) (U := sigma X);
      [reflexivity | apply Hsig | lia].
  - f_equal.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - f_equal. apply IH1; assumption.
Qed.

Lemma subst_all_open_tm_rec : forall t sigma_ty sigma_tm k x,
  (forall y, lc_tm_at 0 0 (sigma_tm y)) ->
  subst_all sigma_ty sigma_tm (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (sigma_tm x) (subst_all sigma_ty sigma_tm t).
Proof.
  induction t as [n | y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
  intros sigma_ty sigma_tm k x Hstm; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite open_tm_rec_lc_id with (K := 0) (k := 0) (j := k) (u := sigma_tm x);
      [reflexivity | apply Hstm | lia].
  - f_equal. apply IH1; assumption.
  - f_equal.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - f_equal. apply IH1; assumption.
  - f_equal. apply IH1; assumption.
  - f_equal.
    + apply IH1; assumption.
    + apply IH2; assumption.
Qed.

Lemma subst_all_open_tm_ty_rec : forall t sigma_ty sigma_tm j X,
  (forall Y, lc_ty_at 0 (sigma_ty Y)) ->
  (forall y, lc_tm_at 0 0 (sigma_tm y)) ->
  subst_all sigma_ty sigma_tm (open_tm_ty_rec j (Ty_FVar X) t) =
  open_tm_ty_rec j (sigma_ty X) (subst_all sigma_ty sigma_tm t).
Proof.
  induction t as [n | y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | t1 IH1 t2 IH2];
  intros sigma_ty sigma_tm j X Hsty Hstm; simpl.
  - reflexivity.
  - rewrite open_tm_ty_rec_lc_id with (K := 0) (k := 0) (j := j) (U := sigma_ty X);
      [reflexivity | apply Hstm | lia].
  - f_equal.
    + apply ty_subst_all_open_ty_rec; assumption.
    + apply IH1; assumption.
  - f_equal.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - f_equal. apply IH1; assumption.
  - f_equal.
    + apply IH1; assumption.
    + apply ty_subst_all_open_ty_rec; assumption.
  - f_equal.
    + apply IH1; assumption.
    + apply IH2; assumption.
Qed.

Lemma sub_ty_id : forall T, ty_subst_all (fun X => Ty_FVar X) T = T.
Proof.
  induction T; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
Qed.

Lemma subst_all_id : forall t,
  subst_all (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply sub_ty_id | assumption].
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; [assumption | apply sub_ty_id].
  - f_equal; assumption.
Qed.

(* The two "environment extension" commutation facts used by the
   fundamental lemma. *)

Lemma lc_tm_fvar_all : forall x K k, lc_tm_at K k (tm_fvar x).
Proof. intros. apply lc_tm_fvar. Qed.

Lemma subst_all_term_extend : forall t sigma_ty sigma_tm x a,
  (forall Y, lc_ty_at 0 (sigma_ty Y)) ->
  (forall y, lc_tm_at 0 0 (sigma_tm y)) ->
  lc_tm_at 0 0 a ->
  ~ In x (fv_tm t) ->
  subst_all sigma_ty (fun y => if Nat.eqb y x then a else sigma_tm y)
    (open_tm_rec 0 (tm_fvar x) t) =
  open_tm_rec 0 a (subst_all sigma_ty sigma_tm t).
Proof.
  intros t sigma_ty sigma_tm x a Hsty Hstm Ha Hfresh.
  rewrite subst_all_open_tm_rec.
  - replace ((if Nat.eqb x x then a else sigma_tm x)) with a.
    + rewrite (subst_all_ext t sigma_ty sigma_ty
                 (fun y => if Nat.eqb y x then a else sigma_tm y) sigma_tm).
      * reflexivity.
      * intros X Hin. reflexivity.
      * intros y Hin. destruct (Nat.eqb y x) eqn:E.
        -- apply Nat.eqb_eq in E. subst y. exfalso. apply Hfresh. assumption.
        -- reflexivity.
    + destruct (Nat.eqb x x) eqn:E; [reflexivity | ].
      apply Nat.eqb_neq in E. exfalso. apply E. reflexivity.
  - intros y. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. assumption.
    + apply Hstm.
Qed.

Lemma subst_all_ty_extend : forall t sigma_ty sigma_tm X U,
  (forall Y, lc_ty_at 0 (sigma_ty Y)) ->
  (forall y, lc_tm_at 0 0 (sigma_tm y)) ->
  lc_ty_at 0 U ->
  ~ In X (fv_tm_ty t) ->
  subst_all (fun Y => if Nat.eqb Y X then U else sigma_ty Y) sigma_tm
    (open_tm_ty_rec 0 (Ty_FVar X) t) =
  open_tm_ty_rec 0 U (subst_all sigma_ty sigma_tm t).
Proof.
  intros t sigma_ty sigma_tm X U Hsty Hstm HU Hfresh.
  rewrite subst_all_open_tm_ty_rec.
  - replace ((if Nat.eqb X X then U else sigma_ty X)) with U.
    + rewrite (subst_all_ext t
                 (fun Y => if Nat.eqb Y X then U else sigma_ty Y) sigma_ty
                 sigma_tm sigma_tm).
      * reflexivity.
      * intros Y Hin. destruct (Nat.eqb Y X) eqn:E.
        -- apply Nat.eqb_eq in E. subst Y. exfalso. apply Hfresh. assumption.
        -- reflexivity.
      * intros y Hin. reflexivity.
    + destruct (Nat.eqb X X) eqn:E; [reflexivity | ].
      apply Nat.eqb_neq in E. exfalso. apply E. reflexivity.
  - intros Y. destruct (Nat.eqb Y X) eqn:E.
    + apply Nat.eqb_eq in E. subst Y. assumption.
    + apply Hsty.
  - assumption.
Qed.

(* ============================================================ *)
(* Reduction, values and context lookup: auxiliary lemmas        *)
(* ============================================================ *)

Lemma value_lc : forall v, value v -> lc_tm_at 0 0 v.
Proof. intros v H. induction H; assumption. Qed.

Lemma multi_trans : forall t1 t2 t3,
  multi t1 t2 -> multi t2 t3 -> multi t1 t3.
Proof.
  intros t1 t2 t3 H12. revert t3.
  induction H12 as [x | x y z Hstep Hrest IHrest]; intros t3 H23.
  - assumption.
  - apply multi_step with y; [assumption | apply IHrest; assumption].
Qed.

Lemma multi_one : forall t1 t2, t1 --> t2 -> t1 -->* t2.
Proof. intros. apply multi_step with t2; [assumption | apply multi_refl]. Qed.

Lemma multi_app_l : forall t1 t1' t2,
  t1 -->* t1' -> lc_tm_at 0 0 t2 -> tm_app t1 t2 -->* tm_app t1' t2.
Proof.
  intros t1 t1' t2 H. induction H as [x | x y z Hstep Hrest IHrest]; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (tm_app y t2).
    + apply ST_App1; assumption.
    + apply IHrest; assumption.
Qed.

Lemma multi_app_r : forall v1 t2 t2',
  value v1 -> t2 -->* t2' -> tm_app v1 t2 -->* tm_app v1 t2'.
Proof.
  intros v1 t2 t2' Hv H. induction H as [x | x y z Hstep Hrest IHrest].
  - apply multi_refl.
  - apply multi_step with (tm_app v1 y).
    + apply ST_App2; assumption.
    + apply IHrest.
Qed.

Lemma multi_tapp : forall t t' T,
  t -->* t' -> lc_ty_at 0 T -> tm_tapp t T -->* tm_tapp t' T.
Proof.
  intros t t' T H. induction H as [x | x y z Hstep Hrest IHrest]; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (tm_tapp y T).
    + apply ST_TApp; assumption.
    + apply IHrest; assumption.
Qed.

Lemma lookup_context_eq : forall Gamma x T,
  lookup_context x ((x, T) :: Gamma) = Some T.
Proof.
  intros. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_context_neq : forall Gamma x y T,
  x <> y -> lookup_context x ((y, T) :: Gamma) = lookup_context x Gamma.
Proof.
  intros. simpl. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma fv_ctx_lookup : forall Gamma x T,
  lookup_context x Gamma = Some T ->
  forall X, In X (fv_ty T) -> In X (fv_ctx Gamma).
Proof.
  induction Gamma as [| [y V] Gamma IH]; intros x T Hlook.
  - simpl in Hlook. discriminate.
  - intros X Hin. simpl in Hlook.
    destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst y. inversion Hlook; subst V.
      simpl. right. apply in_or_app. left. assumption.
    + simpl. right. apply in_or_app. right.
      apply (IH x T Hlook X Hin).
Qed.

(* ============================================================ *)
(* The logical relation                                          *)
(* ============================================================ *)

Definition sem : Type := tm -> Prop.

(* Interpretation of the levels corresponding to enclosing type
   abstractions (de Bruijn index 0 = innermost). *)
Fixpoint lvl (xi : list sem) (i : nat) : sem :=
  match xi with
  | [] => fun _ => False
  | P :: xi' =>
      match i with
      | 0 => P
      | S j => lvl xi' j
      end
  end.

(* Value interpretation of a type. *)
Fixpoint V (rho : atom -> sem) (xi : list sem) (T : ty) : sem :=
  match T with
  | Ty_BVar i => lvl xi i
  | Ty_FVar X => rho X
  | Ty_Arrow T1 T2 =>
      fun t => forall a,
        (exists v, multi a v /\ value v /\ V rho xi T1 v) ->
        (exists v, multi (tm_app t a) v /\ value v /\ V rho xi T2 v)
  | Ty_All T1 =>
      fun t => forall U R0,
        lc_ty_at 0 U ->
        (exists v, multi (tm_tapp t U) v /\ value v /\ V rho (R0 :: xi) T1 v)
  end.

(* Term relation: reduces to a value in the value interpretation. *)
Definition R (rho : atom -> sem) (xi : list sem) (T : ty) : sem :=
  fun t => exists v, multi t v /\ value v /\ V rho xi T v.

(* ---------- level environment lemmas ---------- *)

Lemma lvl_0 : forall P xi, lvl (P :: xi) 0 = P.
Proof. reflexivity. Qed.

Lemma lvl_S : forall P xi i, lvl (P :: xi) (S i) = lvl xi i.
Proof. reflexivity. Qed.

Lemma lvl_app_lt : forall xi1 xi2 i,
  i < length xi1 -> lvl (xi1 ++ xi2) i = lvl xi1 i.
Proof.
  induction xi1 as [| P xi1 IH]; intros xi2 i Hlt; simpl in *.
  - lia.
  - destruct i as [| i].
    + reflexivity.
    + simpl. apply IH. lia.
Qed.

Lemma lvl_app_ge : forall xi1 xi2 i,
  length xi1 <= i -> lvl (xi1 ++ xi2) i = lvl xi2 (i - length xi1).
Proof.
  induction xi1 as [| P xi1 IH]; intros xi2 i Hge; simpl in *.
  - rewrite Nat.sub_0_r. reflexivity.
  - destruct i as [| i].
    + lia.
    + simpl. rewrite IH by lia. reflexivity.
Qed.

Lemma lvl_app_at : forall pre P xi,
  lvl (pre ++ P :: xi) (length pre) = P.
Proof.
  intros. rewrite lvl_app_ge by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.

(* ---------- extensionality and environment lemmas ---------- *)

Lemma R_of_V_iff : forall rho1 rho2 xi1 xi2 T1 T2,
  (forall v, V rho1 xi1 T1 v <-> V rho2 xi2 T2 v) ->
  forall t, R rho1 xi1 T1 t <-> R rho2 xi2 T2 t.
Proof.
  intros rho1 rho2 xi1 xi2 T1 T2 Hiff t. unfold R.
  split.
  - intros (v & Hm & Hv & HV). exists v.
    split; [assumption | split; [assumption | apply Hiff; assumption]].
  - intros (v & Hm & Hv & HV). exists v.
    split; [assumption | split; [assumption | apply Hiff; assumption]].
Qed.

Lemma V_arrow_congr : forall (P1 P1' P2 P2' : sem),
  (forall v, P1 v <-> P1' v) ->
  (forall v, P2 v <-> P2' v) ->
  forall t,
    (forall a,
       (exists v, multi a v /\ value v /\ P1 v) ->
       (exists v, multi (tm_app t a) v /\ value v /\ P2 v)) <->
    (forall a,
       (exists v, multi a v /\ value v /\ P1' v) ->
       (exists v, multi (tm_app t a) v /\ value v /\ P2' v)).
Proof.
  intros P1 P1' P2 P2' H1 H2 t. split; intros H a Ha.
  - destruct Ha as (v & Hm & Hv & HV).
    assert (HV' : P1 v) by (apply (proj2 (H1 v)); assumption).
    destruct (H a (ex_intro _ v (conj Hm (conj Hv HV')))) as (v' & Hm' & Hv' & HV'').
    exists v'. split; [assumption | split; [assumption |]].
    apply (proj1 (H2 v')); assumption.
  - destruct Ha as (v & Hm & Hv & HV).
    assert (HV' : P1' v) by (apply (proj1 (H1 v)); assumption).
    destruct (H a (ex_intro _ v (conj Hm (conj Hv HV')))) as (v' & Hm' & Hv' & HV'').
    exists v'. split; [assumption | split; [assumption |]].
    apply (proj2 (H2 v')); assumption.
Qed.

Lemma V_all_congr : forall (rho1 rho2 : atom -> sem) T1 T2 xi1 xi2 t,
  (forall R0 v, V rho1 (R0 :: xi1) T1 v <-> V rho2 (R0 :: xi2) T2 v) ->
  forall U R0, lc_ty_at 0 U ->
    ((exists v, multi (tm_tapp t U) v /\ value v /\ V rho1 (R0 :: xi1) T1 v) <->
     (exists v, multi (tm_tapp t U) v /\ value v /\ V rho2 (R0 :: xi2) T2 v)).
Proof.
  intros rho1 rho2 T1 T2 xi1 xi2 t Hiff U R0 Hlc.
  split.
  - intros (v & Hm & Hv & HV). exists v.
    split; [assumption | split; [assumption |]].
    apply (proj1 (Hiff R0 v)); assumption.
  - intros (v & Hm & Hv & HV). exists v.
    split; [assumption | split; [assumption |]].
    apply (proj2 (Hiff R0 v)); assumption.
Qed.

Lemma V_lc_env : forall n T, lc_ty_at n T ->
  forall rho xi xi',
    (forall i, i < n -> lvl xi i = lvl xi' i) ->
    forall t, V rho xi T t <-> V rho xi' T t.
Proof.
  intros n T H. induction H as [k i Hi | k X | k T1 T2 H1 IH1 H2 IH2 | k T1 H1 IH1];
  intros rho xi xi' Hagree t; simpl.
  - rewrite (Hagree i Hi). tauto.
  - tauto.
  - apply V_arrow_congr.
    + intros v. apply IH1. assumption.
    + intros v. apply IH2. assumption.
  - assert (Hiff : forall R0 v, V rho (R0 :: xi) T1 v <-> V rho (R0 :: xi') T1 v).
    { intros R0 v. apply IH1. intros i Hi. destruct i as [| i]; simpl.
      - reflexivity.
      - apply Hagree. lia. }
    split; intros H U R0 Hlc.
    + apply (proj1 (V_all_congr rho rho T1 T1 xi xi' t Hiff U R0 Hlc)).
      apply H. assumption.
    + apply (proj2 (V_all_congr rho rho T1 T1 xi xi' t Hiff U R0 Hlc)).
      apply H. assumption.
Qed.

Lemma R_lc_env : forall n T, lc_ty_at n T ->
  forall rho xi xi',
    (forall i, i < n -> lvl xi i = lvl xi' i) ->
    forall t, R rho xi T t <-> R rho xi' T t.
Proof.
  intros n T Hlc rho xi xi' Hagree t.
  apply (R_of_V_iff rho rho xi xi' T T). intros v.
  apply V_lc_env with (n := n); assumption.
Qed.

Lemma V_ext : forall T,
  forall rho1 rho2 xi,
    (forall X, In X (fv_ty T) -> forall t, rho1 X t <-> rho2 X t) ->
    forall t, V rho1 xi T t <-> V rho2 xi T t.
Proof.
  induction T as [j | X | T1 IH1 T2 IH2 | T1 IH1];
  intros rho1 rho2 xi Hext t; simpl.
  - tauto.
  - apply Hext. simpl. left. reflexivity.
  - apply V_arrow_congr.
    + intros v. apply IH1.
      intros Y HY. apply Hext. apply in_or_app. left. assumption.
    + intros v. apply IH2.
      intros Y HY. apply Hext. apply in_or_app. right. assumption.
  - assert (Hiff : forall R0 v, V rho1 (R0 :: xi) T1 v <-> V rho2 (R0 :: xi) T1 v).
    { intros R0 v. apply IH1. assumption. }
    split; intros H U R0 Hlc.
    + apply (proj1 (V_all_congr rho1 rho2 T1 T1 xi xi t Hiff U R0 Hlc)).
      apply H. assumption.
    + apply (proj2 (V_all_congr rho1 rho2 T1 T1 xi xi t Hiff U R0 Hlc)).
      apply H. assumption.
Qed.

Lemma R_ext : forall T,
  forall rho1 rho2 xi,
    (forall X, In X (fv_ty T) -> forall t, rho1 X t <-> rho2 X t) ->
    forall t, R rho1 xi T t <-> R rho2 xi T t.
Proof.
  intros T rho1 rho2 xi Hext t.
  apply (R_of_V_iff rho1 rho2 xi xi T T). intros v.
  exact (V_ext T rho1 rho2 xi Hext v).
Qed.

(* Opening a type variable in the interpretation. *)
Lemma V_open_ty_rec : forall T k U,
  lc_ty_at (S k) T -> lc_ty_at 0 U ->
  forall rho xi pre, length pre = k ->
  forall t, V rho (pre ++ xi) (open_ty_rec k U T) t <->
            V rho (pre ++ V rho xi U :: xi) T t.
Proof.
  induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1];
  intros k U Hlc HU rho xi pre Hlen t; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i.
      simpl. rewrite <- Hlen. rewrite lvl_app_at.
      apply V_lc_env with (n := 0); [assumption | intros j Hj; lia].
    + apply Nat.eqb_neq in E.
      inversion Hlc; subst.
      assert (Hi : i < length pre) by lia.
      simpl.
      rewrite (lvl_app_lt pre xi i Hi).
      rewrite (lvl_app_lt pre (V rho xi U :: xi) i Hi).
      tauto.
  - tauto.
  - inversion Hlc; subst.
    apply V_arrow_congr.
    + intros v. apply IH1; auto.
    + intros v. apply IH2; auto.
  - inversion Hlc; subst.
    assert (Hiff : forall R0 v,
      V rho (R0 :: (pre ++ xi)) (open_ty_rec (S (length pre)) U T1) v <->
      V rho (R0 :: (pre ++ V rho xi U :: xi)) T1 v).
    { intros R0 v.
      apply IH1 with (U := U) (pre := R0 :: pre); auto. }
    split; intros H U' R0 HlcU.
    + apply (proj1 (V_all_congr rho rho (open_ty_rec (S (length pre)) U T1) T1 (pre ++ xi) (pre ++ V rho xi U :: xi) t Hiff U' R0 HlcU)).
      apply H. assumption.
    + apply (proj2 (V_all_congr rho rho (open_ty_rec (S (length pre)) U T1) T1 (pre ++ xi) (pre ++ V rho xi U :: xi) t Hiff U' R0 HlcU)).
      apply H. assumption.
Qed.

Lemma R_open_ty_rec : forall T k U,
  lc_ty_at (S k) T -> lc_ty_at 0 U ->
  forall rho xi pre, length pre = k ->
  forall t, R rho (pre ++ xi) (open_ty_rec k U T) t <->
            R rho (pre ++ V rho xi U :: xi) T t.
Proof.
  intros T k U Hlc HU rho xi pre Hlen t.
  apply (R_of_V_iff rho rho (pre ++ xi) (pre ++ V rho xi U :: xi) (open_ty_rec k U T) T). intros v.
  apply V_open_ty_rec; assumption.
Qed.

(* ============================================================ *)
(* Local closure of typable terms and types                      *)
(* ============================================================ *)

Lemma not_in_first : forall (l1 l2 : list atom) x,
  ~ In x (l1 ++ l2) -> ~ In x l1.
Proof. intros l1 l2 x H Hin. apply H. apply in_or_app. left. assumption. Qed.

Lemma not_in_second : forall (l1 l2 : list atom) x,
  ~ In x (l1 ++ l2) -> ~ In x l2.
Proof. intros l1 l2 x H Hin. apply H. apply in_or_app. right. assumption. Qed.

Lemma has_type_lc_ty : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H.
  induction H as [Delta Gamma x T Hlook Hwf
                 | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
                 | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta Gamma t T1 Hbody IHbody
                 | Delta Gamma t T U H1 IH1 HwfU
                 | Delta Gamma t1 t2 T H1 IH1 H2 IH2].
  - exact (wf_ty_lc Delta T Hwf).
  - apply lc_ty_arrow.
    + exact (wf_ty_lc Delta T1 Hwf).
    + apply (IHbody (fresh L)). apply fresh_not_in.
  - inversion IH1. assumption.
  - apply lc_ty_all.
    change (lc_ty_at 1 T1).
    apply (lc_ty_at_open_inv T1 0 (Ty_FVar (fresh L))).
    change (lc_ty_at 0 (open_ty T1 (Ty_FVar (fresh L)))).
    apply (IHbody (fresh L)). apply fresh_not_in.
  - apply (lc_ty_at_open T 0 U).
    + inversion IH1. assumption.
    + exact (wf_ty_lc Delta U HwfU).
  - assumption.
Qed.

Lemma has_type_lc_tm : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at 0 0 t.
Proof.
  intros Delta Gamma t T H.
  induction H as [Delta Gamma x T Hlook Hwf
                 | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
                 | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta Gamma t T1 Hbody IHbody
                 | Delta Gamma t T U H1 IH1 HwfU
                 | Delta Gamma t1 t2 T H1 IH1 H2 IH2].
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + exact (wf_ty_lc Delta T1 Hwf).
    + apply (lc_tm_at_open_tm_inv t2 0 0 (fresh L)).
      change (lc_tm_at 0 0 (open_tm t2 (tm_fvar (fresh L)))).
      apply (IHbody (fresh L)). apply fresh_not_in.
  - apply lc_tm_app; assumption.
  - apply lc_tm_tabs.
    apply (lc_tm_at_open_tm_ty_inv t 0 0 0 (Ty_FVar (fresh L))).
    + lia.
    + change (lc_tm_at 0 0 (open_tm_ty t (Ty_FVar (fresh L)))).
      apply (IHbody (fresh L)). apply fresh_not_in.
  - apply lc_tm_tapp.
    + assumption.
    + exact (wf_ty_lc Delta U HwfU).
  - apply lc_tm_choice; assumption.
Qed.

(* ============================================================ *)
Lemma fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall sigma_ty rho sigma_tm,
    (forall X, lc_ty_at 0 (sigma_ty X)) ->
    (forall y, lc_tm_at 0 0 (sigma_tm y)) ->
    (forall x V0, lookup_context x Gamma = Some V0 -> R rho [] V0 (sigma_tm x)) ->
    R rho [] T (subst_all sigma_ty sigma_tm t).
Proof.
  intros Delta Gamma t T H.
  induction H as [Delta Gamma x T Hlook Hwf
                 | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
                 | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta Gamma tb T1 Hbody IHbody
                 | Delta Gamma t T U H1 IH1 HwfU
                 | Delta Gamma t1 t2 T H1 IH1 H2 IH2];
  intros sigma_ty rho sigma_tm Hsty Hstm Henv.
  - (* T_Var *)
    change (R rho [] T (sigma_tm x)).
    apply Henv. assumption.
  - (* T_Abs *)
    unfold R.
    exists (tm_abs (ty_subst_all sigma_ty T1) (subst_all sigma_ty sigma_tm t2)).
    split.
    + apply multi_refl.
    + split.
      * apply v_abs.
        apply (lc_tm_at_subst_all (tm_abs T1 t2) sigma_ty sigma_tm 0 0).
        -- apply has_type_lc_tm with (Delta := Delta) (Gamma := Gamma)
             (T := Ty_Arrow T1 T2).
           apply T_Abs with (L := L); assumption.
        -- exact Hsty.
        -- exact Hstm.
      * intros a (a' & Hma & Hva & HVa).
        pose (bad := L ++ (fv_ctx Gamma ++ fv_tm t2)).
        assert (Hxbad : ~ In (fresh bad) bad) by apply fresh_not_in.
        assert (HxL : ~ In (fresh bad) L).
        { apply (not_in_first L (fv_ctx Gamma ++ fv_tm t2)); exact Hxbad. }
        assert (Hxctx : ~ In (fresh bad) (fv_ctx Gamma)).
        { apply (not_in_first (fv_ctx Gamma) (fv_tm t2)).
          apply (not_in_second L (fv_ctx Gamma ++ fv_tm t2)); exact Hxbad. }
        assert (Hxtm : ~ In (fresh bad) (fv_tm t2)).
        { apply (not_in_second (fv_ctx Gamma) (fv_tm t2)).
          apply (not_in_second L (fv_ctx Gamma ++ fv_tm t2)); exact Hxbad. }
        assert (Hstm' : forall y,
          lc_tm_at 0 0 (if Nat.eqb y (fresh bad) then a' else sigma_tm y)).
        { intros y. destruct (Nat.eqb y (fresh bad)) eqn:E.
          - apply value_lc. exact Hva.
          - apply Hstm. }
        assert (Henv' : forall y V0,
          lookup_context y ((fresh bad, T1) :: Gamma) = Some V0 ->
          R rho [] V0 (if Nat.eqb y (fresh bad) then a' else sigma_tm y)).
        { intros y V0 Hlook.
          destruct (Nat.eqb y (fresh bad)) eqn:E.
          - apply Nat.eqb_eq in E. subst y.
            simpl in Hlook.
            rewrite (Nat.eqb_refl (max_list bad)) in Hlook.
            simpl in Hlook.
            inversion Hlook; subst V0.
            unfold R. exists a'. split; [apply multi_refl | split; [exact Hva | exact HVa]].
          - assert (Hne : y <> fresh bad) by (apply Nat.eqb_neq; exact E).
            assert (Hneq : lookup_context y ((fresh bad, T1) :: Gamma) = lookup_context y Gamma).
            { apply lookup_context_neq. assumption. }
            rewrite Hneq in Hlook.
            apply Henv. assumption. }
        pose proof
          (IHbody (fresh bad) HxL sigma_ty rho
             (fun y => if Nat.eqb y (fresh bad) then a' else sigma_tm y)
             Hsty Hstm' Henv') as HIH.
        change (R rho [] T2
                  (subst_all sigma_ty
                     (fun y => if Nat.eqb y (fresh bad) then a' else sigma_tm y)
                     (open_tm_rec 0 (tm_fvar (fresh bad)) t2))) in HIH.
        rewrite (subst_all_term_extend t2 sigma_ty sigma_tm (fresh bad) a'
                   Hsty Hstm (value_lc a' Hva) Hxtm) in HIH.
        unfold R in HIH. destruct HIH as (w & Hmw & Hvw & HVw).
        exists w. split.
        -- eapply multi_trans.
           ++ apply multi_app_r.
              ** apply v_abs.
                 apply (lc_tm_at_subst_all (tm_abs T1 t2) sigma_ty sigma_tm 0 0).
                 --- apply has_type_lc_tm with (Delta := Delta) (Gamma := Gamma)
                       (T := Ty_Arrow T1 T2).
                     apply T_Abs with (L := L); assumption.
                 --- exact Hsty.
                 --- exact Hstm.
              ** exact Hma.
           ++ eapply multi_trans.
              ** apply multi_one. apply ST_AppAbs.
                 --- apply (lc_tm_at_subst_all (tm_abs T1 t2) sigma_ty sigma_tm 0 0).
                     +++ apply has_type_lc_tm with (Delta := Delta) (Gamma := Gamma)
                           (T := Ty_Arrow T1 T2).
                         apply T_Abs with (L := L); assumption.
                     +++ exact Hsty.
                     +++ exact Hstm.
                 --- exact Hva.
              ** exact Hmw.
        -- split; [exact Hvw | exact HVw].
  - (* T_App *)
    pose proof (IH1 sigma_ty rho sigma_tm Hsty Hstm Henv) as HR1.
    pose proof (IH2 sigma_ty rho sigma_tm Hsty Hstm Henv) as HR2.
    unfold R in HR1. destruct HR1 as (v1 & Hm1 & Hv1 & HV1).
    simpl in HV1.
    pose proof (HV1 (subst_all sigma_ty sigma_tm t2) HR2) as HR3.
    unfold R in HR3. destruct HR3 as (w & Hmw & Hvw & HVw).
    unfold R. exists w. split.
    + eapply multi_trans.
      * apply multi_app_l.
        -- exact Hm1.
        -- apply (lc_tm_at_subst_all t2 sigma_ty sigma_tm 0 0).
           ++ apply has_type_lc_tm with (Delta := Delta) (Gamma := Gamma) (T := T1).
              exact H2.
           ++ exact Hsty.
           ++ exact Hstm.
      * exact Hmw.
    + split; [exact Hvw | exact HVw].
  - (* T_TAbs *)
    unfold R.
    exists (tm_tabs (subst_all sigma_ty sigma_tm tb)).
    split.
    + apply multi_refl.
    + split.
      * apply v_tabs.
        apply (lc_tm_at_subst_all (tm_tabs tb) sigma_ty sigma_tm 0 0).
        -- apply has_type_lc_tm with (Delta := Delta) (Gamma := Gamma) (T := Ty_All T1).
           apply T_TAbs with (L := L); assumption.
        -- exact Hsty.
        -- exact Hstm.
      * intros U R0 HlcU.
        pose (bad := L ++ (fv_ctx Gamma ++ (fv_ty T1 ++ fv_tm_ty tb))).
        assert (Hxbad : ~ In (fresh bad) bad) by apply fresh_not_in.
        assert (HxL : ~ In (fresh bad) L).
        { apply (not_in_first L (fv_ctx Gamma ++ (fv_ty T1 ++ fv_tm_ty tb))); exact Hxbad. }
        assert (Hxctx : ~ In (fresh bad) (fv_ctx Gamma)).
        { apply (not_in_first (fv_ctx Gamma) (fv_ty T1 ++ fv_tm_ty tb)).
          apply (not_in_second L (fv_ctx Gamma ++ (fv_ty T1 ++ fv_tm_ty tb))); exact Hxbad. }
        assert (HxT1 : ~ In (fresh bad) (fv_ty T1)).
        { apply (not_in_first (fv_ty T1) (fv_tm_ty tb)).
          apply (not_in_second (fv_ctx Gamma) (fv_ty T1 ++ fv_tm_ty tb)).
          apply (not_in_second L (fv_ctx Gamma ++ (fv_ty T1 ++ fv_tm_ty tb))); exact Hxbad. }
        assert (HxT : ~ In (fresh bad) (fv_tm_ty tb)).
        { apply (not_in_second (fv_ty T1) (fv_tm_ty tb)).
          apply (not_in_second (fv_ctx Gamma) (fv_ty T1 ++ fv_tm_ty tb)).
          apply (not_in_second L (fv_ctx Gamma ++ (fv_ty T1 ++ fv_tm_ty tb))); exact Hxbad. }
        assert (Hsty' : forall Y,
          lc_ty_at 0 (if Nat.eqb Y (fresh bad) then U else sigma_ty Y)).
        { intros Y. destruct (Nat.eqb Y (fresh bad)) eqn:E.
          - exact HlcU.
          - apply Hsty. }
        assert (Henv' : forall y V0,
          lookup_context y Gamma = Some V0 ->
          R (fun Y => if Nat.eqb Y (fresh bad) then R0 else rho Y) [] V0 (sigma_tm y)).
        { intros y V0 Hlook.
          assert (Hext0 : forall Y, In Y (fv_ty V0) -> forall t : tm,
                    (if Nat.eqb Y (fresh bad) then R0 else rho Y) t <-> rho Y t).
          { intros Y HY. destruct (Nat.eqb Y (fresh bad)) eqn:E.
            - apply Nat.eqb_eq in E. exfalso.
              apply Hxctx. rewrite <- E. apply (fv_ctx_lookup Gamma y V0 Hlook Y HY).
            - tauto. }
          apply (proj2 (R_ext V0
                          (fun Y => if Nat.eqb Y (fresh bad) then R0 else rho Y)
                          rho [] Hext0 (sigma_tm y))).
          apply Henv. assumption. }
        pose proof
          (IHbody (fresh bad) HxL
             (fun Y => if Nat.eqb Y (fresh bad) then U else sigma_ty Y)
             (fun Y => if Nat.eqb Y (fresh bad) then R0 else rho Y)
             sigma_tm Hsty' Hstm Henv') as HIH.
        change (R (fun Y => if Nat.eqb Y (fresh bad) then R0 else rho Y) []
                  (open_ty T1 (Ty_FVar (fresh bad)))
                  (subst_all (fun Y => if Nat.eqb Y (fresh bad) then U else sigma_ty Y)
                     sigma_tm
                     (open_tm_ty_rec 0 (Ty_FVar (fresh bad)) tb))) in HIH.
        rewrite (subst_all_ty_extend tb sigma_ty sigma_tm (fresh bad) U
                   Hsty Hstm HlcU HxT) in HIH.
        assert (HlcT1 : lc_ty_at 1 T1).
        { pose proof (has_type_lc_ty Delta Gamma (tm_tabs tb) (Ty_All T1)
                        (T_TAbs L Delta Gamma tb T1 Hbody)) as Hl.
          inversion Hl. assumption. }
        assert (Hstep1 : R (fun Y => if Nat.eqb Y (fresh bad) then R0 else rho Y)
                          (V (fun Y => if Nat.eqb Y (fresh bad) then R0 else rho Y)
                             [] (Ty_FVar (fresh bad)) :: [])
                          T1 (open_tm_ty_rec 0 U (subst_all sigma_ty sigma_tm tb))).
        { apply (proj1 (R_open_ty_rec T1 0 (Ty_FVar (fresh bad)) HlcT1
                          (lc_ty_fvar 0 (fresh bad))
                          (fun Y => if Nat.eqb Y (fresh bad) then R0 else rho Y)
                          [] [] eq_refl
                          (open_tm_ty_rec 0 U (subst_all sigma_ty sigma_tm tb)))).
          exact HIH. }
        assert (Hstep2 : R (fun Y => if Nat.eqb Y (fresh bad) then R0 else rho Y)
                          (R0 :: [])
                          T1 (open_tm_ty_rec 0 U (subst_all sigma_ty sigma_tm tb))).
        { unfold R in Hstep1. unfold R.
          simpl in Hstep1. rewrite (Nat.eqb_refl (max_list bad)) in Hstep1. simpl in Hstep1.
          exact Hstep1. }
        assert (Hext1 : forall Y, In Y (fv_ty T1) -> forall t : tm,
                  (if Nat.eqb Y (fresh bad) then R0 else rho Y) t <-> rho Y t).
        { intros Y HY. destruct (Nat.eqb Y (fresh bad)) eqn:E.
          - apply Nat.eqb_eq in E. exfalso. apply HxT1. rewrite <- E. assumption.
          - tauto. }
        assert (Hconv : R rho (R0 :: [])
                          T1 (open_tm_ty_rec 0 U (subst_all sigma_ty sigma_tm tb))).
        { apply (proj1 (R_ext T1
                          (fun Y => if Nat.eqb Y (fresh bad) then R0 else rho Y)
                          rho (R0 :: []) Hext1
                          (open_tm_ty_rec 0 U (subst_all sigma_ty sigma_tm tb)))).
          exact Hstep2. }
        unfold R in Hconv. destruct Hconv as (w & Hmw & Hvw & HVw).
        exists w. split.
        -- eapply multi_trans.
           ++ apply multi_one. apply ST_TAppTabs.
              ** apply (lc_tm_at_subst_all (tm_tabs tb) sigma_ty sigma_tm 0 0).
                 --- apply has_type_lc_tm with (Delta := Delta) (Gamma := Gamma)
                       (T := Ty_All T1).
                     apply T_TAbs with (L := L); assumption.
                 --- exact Hsty.
                 --- exact Hstm.
              ** exact HlcU.
           ++ exact Hmw.
        -- split; [exact Hvw | exact HVw].
  - (* T_TApp *)
    pose proof (IH1 sigma_ty rho sigma_tm Hsty Hstm Henv) as HR1.
    unfold R in HR1. destruct HR1 as (v0 & Hm0 & Hv0 & HV0).
    simpl in HV0.
    assert (HlcU : lc_ty_at 0 U) by (apply (wf_ty_lc Delta U HwfU)).
    assert (HlcSU : lc_ty_at 0 (ty_subst_all sigma_ty U)).
    { apply (lc_ty_at_ty_subst_all U sigma_ty 0 (wf_ty_lc Delta U HwfU) Hsty). }
    pose proof (HV0 (ty_subst_all sigma_ty U) (V rho [] U) HlcSU) as HR2.
    destruct HR2 as (w & Hmw & Hvw & HVw).
    assert (HlcT : lc_ty_at 1 T).
    { pose proof (has_type_lc_ty Delta Gamma t (Ty_All T) H1) as Hl.
      inversion Hl. assumption. }
    unfold R. exists w. split.
    + eapply multi_trans.
      * apply multi_tapp.
        -- exact Hm0.
        -- exact HlcSU.
      * exact Hmw.
    + split; [exact Hvw |].
      apply (proj2 (V_open_ty_rec T 0 U HlcT HlcU rho [] [] eq_refl w)).
      exact HVw.
  - (* T_Choice *)
    pose proof (IH1 sigma_ty rho sigma_tm Hsty Hstm Henv) as HR1.
    unfold R in HR1. destruct HR1 as (v & Hmv & Hvv & HVv).
    unfold R. exists v. split.
    + eapply multi_trans.
      * apply multi_one. apply ST_ChoiceLeft.
        -- apply (lc_tm_at_subst_all t1 sigma_ty sigma_tm 0 0).
           ++ exact (has_type_lc_tm Delta Gamma t1 T H1).
           ++ exact Hsty.
           ++ exact Hstm.
        -- apply (lc_tm_at_subst_all t2 sigma_ty sigma_tm 0 0).
           ++ exact (has_type_lc_tm Delta Gamma t2 T H2).
           ++ exact Hsty.
           ++ exact Hstm.
      * exact Hmv.
    + split; [exact Hvv | exact HVv].
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
  intros t Ht U v HwfU Hvalv HvU.
  assert (Henv : forall x V0, lookup_context x empty = Some V0 ->
                 R (fun (_ : atom) (_ : tm) => False) [] V0 (tm_fvar x)).
  { intros x V0 Hlook. simpl in Hlook. discriminate. }
  pose proof
    (fundamental [] empty t (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht
       (fun X => Ty_FVar X)
       (fun (_ : atom) (_ : tm) => False)
       (fun x => tm_fvar x)
       (fun X => lc_ty_fvar 0 X)
       (fun y => lc_tm_fvar 0 0 y)
       Henv) as HR.
  rewrite subst_all_id in HR.
  unfold R in HR. destruct HR as (v0 & Hm0 & Hv0 & HV0).
  simpl in HV0.
  assert (HlcU : lc_ty_at 0 U) by (apply (wf_ty_lc [] U HwfU)).
  pose proof (HV0 U (fun a => a = v) HlcU) as HR1.
  unfold R in HR1. destruct HR1 as (w & Hmw & Hvw & HVw).
  simpl in HVw.
  assert (HRv : R (fun (_ : atom) (_ : tm) => False) [fun a => a = v]
                 (Ty_BVar 0) v).
  { unfold R. exists v. split; [apply multi_refl | split; [exact Hvalv |]].
    simpl. reflexivity. }
  pose proof (HVw v HRv) as HR2.
  unfold R in HR2. destruct HR2 as (u & Hmu & Hvu & HVu).
  simpl in HVu. subst u.
  assert (Hchain : tm_tapp t U -->* w).
  { eapply multi_trans.
    - apply multi_tapp; [exact Hm0 | exact HlcU].
    - exact Hmw. }
  eapply multi_trans.
  - apply multi_app_l; [exact Hchain | apply value_lc; exact Hvalv].
  - exact Hmu.
Qed.

End SystemFParametricityNondeterminismHardTask.
