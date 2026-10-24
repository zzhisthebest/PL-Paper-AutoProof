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
(* Preliminary: freshness and free variables                     *)
(* ============================================================ *)

Fixpoint max_list (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Lemma max_list_ge : forall L x, In x L -> x <= max_list L.
Proof.
  induction L as [| y ys IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_list ys); auto. apply Nat.le_max_r.
Qed.

Definition fresh_from (L : list atom) : atom := S (max_list L).

Lemma fresh_from_notin : forall L, ~ In (fresh_from L) L.
Proof.
  intros L Hin. unfold fresh_from in Hin.
  pose proof (max_list_ge L _ Hin). lia.
Qed.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All Tb => fv_ty Tb
  end.

Fixpoint fv_tm_ann (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar _ => []
  | tm_abs T b => fv_ty T ++ fv_tm_ann b
  | tm_app t1 t2 => fv_tm_ann t1 ++ fv_tm_ann t2
  | tm_tabs b => fv_tm_ann b
  | tm_tapp t T => fv_tm_ann t ++ fv_ty T
  | tm_choice t1 t2 => fv_tm_ann t1 ++ fv_tm_ann t2
  end.

Definition context_fv (Gamma : context) : list atom :=
  flat_map (fun p => fv_ty (snd p)) Gamma.

(* ============================================================ *)
(* Locally closed types: monotonicity and opening lemmas          *)
(* ============================================================ *)

Lemma lc_ty_at_mono : forall T k k',
  k <= k' -> lc_ty_at k T -> lc_ty_at k' T.
Proof.
  induction T; intros k k' Hle Hlc; inversion Hlc; subst; eauto using lc_ty_at.
  - (* BVar *) apply lc_ty_bvar. lia.
  - (* All *) apply lc_ty_all. refine (IHT (S k) (S k') _ _); [lia | assumption].
Qed.

Lemma lc_ty_at_weaken_bvar : forall k T, lc_ty_at k T -> lc_ty_at (S k) T.
Proof. intros k T H. exact (lc_ty_at_mono T k (S k) ltac:(lia) H). Qed.

Lemma lc_tm_at_mono : forall t K K' k k',
  K <= K' -> k <= k' -> lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  induction t; intros K K' k k' HK Hk Hlc; inversion Hlc; subst;
    eauto using lc_tm_at, lc_ty_at_mono.
  - (* bvar *) apply lc_tm_bvar. lia.
  - (* abs *) apply lc_tm_abs.
    + exact (lc_ty_at_mono t K K' HK ltac:(eassumption)).
    + refine (IHt K K' (S k) (S k') _ _ _); [lia | lia | eassumption].
  - (* tabs *) apply lc_tm_tabs.
    refine (IHt (S K) (S K') k k' _ _ _); [lia | lia | eassumption].
Qed.

(* Forward opening of a term variable *)
Lemma lc_tm_open_fvar : forall t K k x,
  lc_tm_at K (S k) t -> lc_tm_at K k (open_tm_rec k (tm_fvar x) t).
Proof.
  induction t; intros K k x Hlc; simpl.
  - (* bvar *) simpl in Hlc. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_fvar.
    + apply Nat.eqb_neq in E. inversion Hlc; subst. apply lc_tm_bvar. lia.
  - (* fvar *) apply lc_tm_fvar.
  - (* abs *) simpl in Hlc. inversion Hlc; subst. apply lc_tm_abs.
    + eassumption.
    + refine (IHt K (S k) x _); eassumption.
  - (* app *) simpl in Hlc. inversion Hlc; subst. apply lc_tm_app; eauto.
  - (* tabs *) simpl in Hlc. inversion Hlc; subst. apply lc_tm_tabs.
    refine (IHt (S K) k x _); eassumption.
  - (* tapp *) simpl in Hlc. inversion Hlc; subst. apply lc_tm_tapp; eauto.
  - (* choice *) simpl in Hlc. inversion Hlc; subst. apply lc_tm_choice; eauto.
Qed.

(* Forward opening of a type variable inside type annotations *)
Lemma lc_ty_open_fvar : forall T K X,
  lc_ty_at (S K) T -> lc_ty_at K (open_ty_rec K (Ty_FVar X) T).
Proof.
  induction T; intros K X Hlc; simpl.
  - (* bvar *) simpl in Hlc. destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_fvar.
    + apply Nat.eqb_neq in E. inversion Hlc; subst. apply lc_ty_bvar. lia.
  - (* fvar *) apply lc_ty_fvar.
  - (* arrow *) simpl in Hlc. inversion Hlc; subst. apply lc_ty_arrow; eauto.
  - (* all *) simpl in Hlc. inversion Hlc; subst. apply lc_ty_all.
    refine (IHT (S K) X _); eassumption.
Qed.

Lemma lc_tm_open_ty_fvar : forall t K k X,
  lc_tm_at (S K) k t -> lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t).
Proof.
  induction t; intros K k X Hlc; simpl.
  - (* bvar *) inversion Hlc; subst. apply lc_tm_bvar. lia.
  - (* fvar *) apply lc_tm_fvar.
  - (* abs *) simpl in Hlc. inversion Hlc; subst. apply lc_tm_abs.
    + eapply lc_ty_open_fvar; eassumption.
    + refine (IHt K (S k) X _); eassumption.
  - (* app *) simpl in Hlc. inversion Hlc; subst. apply lc_tm_app; eauto.
  - (* tabs *) simpl in Hlc. inversion Hlc; subst. apply lc_tm_tabs.
    refine (IHt (S K) k X _); eassumption.
  - (* tapp *) simpl in Hlc. inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eassumption.
    + eapply lc_ty_open_fvar; eassumption.
  - (* choice *) simpl in Hlc. inversion Hlc; subst. apply lc_tm_choice; eauto.
Qed.

(* Inverse opening lemmas *)
Lemma lc_tm_open_fvar_inv : forall t K j x,
  lc_tm_at K j (open_tm_rec j (tm_fvar x) t) -> lc_tm_at K (S j) t.
Proof.
  induction t; intros K j x Hlc; simpl in Hlc.
  - (* bvar *) destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar. lia.
    + apply Nat.eqb_neq in E. inversion Hlc; subst. apply lc_tm_bvar. lia.
  - (* fvar *) apply lc_tm_fvar.
  - (* abs *) inversion Hlc; subst. apply lc_tm_abs.
    + eassumption.
    + refine (IHt K (S j) x _); eassumption.
  - (* app *) inversion Hlc; subst. apply lc_tm_app; eauto.
  - (* tabs *) inversion Hlc; subst. apply lc_tm_tabs.
    refine (IHt (S K) j x _); eassumption.
  - (* tapp *) inversion Hlc; subst. apply lc_tm_tapp; eauto.
  - (* choice *) inversion Hlc; subst. apply lc_tm_choice; eauto.
Qed.

Lemma lc_ty_open_fvar_inv : forall T K X,
  lc_ty_at K (open_ty_rec K (Ty_FVar X) T) -> lc_ty_at (S K) T.
Proof.
  induction T; intros K X Hlc; simpl in Hlc.
  - (* bvar *) destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + apply Nat.eqb_neq in E. inversion Hlc; subst. apply lc_ty_bvar. lia.
  - (* fvar *) inversion Hlc; subst. apply lc_ty_fvar.
  - (* arrow *) inversion Hlc; subst. apply lc_ty_arrow; eauto.
  - (* all *) inversion Hlc; subst. apply lc_ty_all.
    refine (IHT (S K) X _); eassumption.
Qed.

Lemma lc_tm_open_ty_fvar_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X Hlc; simpl in Hlc.
  - (* bvar *) inversion Hlc; subst. apply lc_tm_bvar. assumption.
  - (* fvar *) apply lc_tm_fvar.
  - (* abs *) inversion Hlc; subst. apply lc_tm_abs.
    + eapply lc_ty_open_fvar_inv; eassumption.
    + refine (IHt K (S k) X _); eassumption.
  - (* app *) inversion Hlc; subst. apply lc_tm_app; eauto.
  - (* tabs *) inversion Hlc; subst. apply lc_tm_tabs.
    refine (IHt (S K) k X _); eassumption.
  - (* tapp *) inversion Hlc; subst. apply lc_tm_tapp.
    + eapply IHt; eassumption.
    + eapply lc_ty_open_fvar_inv; eassumption.
  - (* choice *) inversion Hlc; subst. apply lc_tm_choice; eauto.
Qed.

(* ============================================================ *)
(* Well-formed types                                            *)
(* ============================================================ *)

Lemma wf_ty_incl : forall Delta T,
  wf_ty Delta T -> forall Delta', (forall X, In X Delta -> In X Delta') -> wf_ty Delta' T.
Proof.
  intros Delta T H. induction H; intros Delta' Hincl.
  - apply WF_Var. apply Hincl. assumption.
  - apply WF_Arrow; auto.
  - apply WF_All with (L := L).
    intros X HX. apply H0 with (Delta' := X :: Delta'); auto.
    intros Y HY. simpl in HY. destruct HY as [-> | HY].
    + simpl. left. reflexivity.
    + simpl. right. apply Hincl. assumption.
Qed.

Lemma wf_ty_weaken : forall Delta T X,
  wf_ty Delta T -> wf_ty (X :: Delta) T.
Proof.
  intros. apply wf_ty_incl with (Delta := Delta); auto.
  intros Y HY. simpl. right. auto.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; auto.
  - (* WF_All *)
    apply lc_ty_all.
    set (X := fresh_from (L ++ Delta)).
    assert (HX : ~ In X (L ++ Delta)) by apply fresh_from_notin.
    assert (HXL : ~ In X L).
    { intro Hin. apply HX. apply in_app_iff. left. assumption. }
    specialize (H0 X HXL).
    apply lc_ty_open_fvar_inv in H0.
    auto.
Qed.


(* ============================================================ *)
(* Type and term substitution                                    *)
(* ============================================================ *)

Fixpoint tsubst (s : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => s X
  | Ty_Arrow T1 T2 => Ty_Arrow (tsubst s T1) (tsubst s T2)
  | Ty_All Tb => Ty_All (tsubst s Tb)
  end.

Fixpoint subst_all (st : atom -> ty) (s : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => s x
  | tm_abs T b => tm_abs (tsubst st T) (subst_all st s b)
  | tm_app t1 t2 => tm_app (subst_all st s t1) (subst_all st s t2)
  | tm_tabs b => tm_tabs (subst_all st s b)
  | tm_tapp t T => tm_tapp (subst_all st s t) (tsubst st T)
  | tm_choice t1 t2 => tm_choice (subst_all st s t1) (subst_all st s t2)
  end.

Definition tvar_update (s : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb Y X then U else s Y.

Definition tmenv_update (s : atom -> tm) (x : atom) (a : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then a else s y.

Lemma tsubst_agree : forall T s s',
  (forall X, In X (fv_ty T) -> s X = s' X) ->
  tsubst s T = tsubst s' T.
Proof.
  induction T; intros s s' Hagree; simpl.
  - reflexivity.
  - apply Hagree. simpl. left. reflexivity.
  - f_equal.
    + apply IHT1. intros X Hin. apply Hagree. simpl. apply in_app_iff. left. assumption.
    + apply IHT2. intros X Hin. apply Hagree. simpl. apply in_app_iff. right. assumption.
  - f_equal. apply IHT. assumption.
Qed.

Lemma tsubst_identity : forall T, tsubst (fun X => Ty_FVar X) T = T.
Proof. induction T; simpl; congruence. Qed.

(* Opening a type whose free bvars are all bound (lc at level 0) is inert. *)
Lemma open_ty_rec_closed : forall T d k U,
  lc_ty_at d T -> open_ty_rec (k + d) U T = T.
Proof.
  induction T; intros d k U Hlc; simpl.
  - (* BVar *) inversion Hlc; subst. destruct (Nat.eqb (k + d) n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - (* Arrow *) inversion Hlc; subst. rewrite IHT1; auto. rewrite IHT2; auto.
  - (* All *) inversion Hlc; subst. f_equal.
    replace (S (k + d)) with (k + S d) by lia.
    apply IHT. assumption.
Qed.

Lemma open_ty_closed : forall T U,
  lc_ty_at 0 T -> open_ty_rec 0 U T = T.
Proof.
  intros. replace 0 with (0 + 0) by lia. apply open_ty_rec_closed; auto.
Qed.

Lemma tsubst_open_ty_rec : forall T s k U,
  (forall X, lc_ty_at 0 (s X)) ->
  tsubst s (open_ty_rec k U T) = open_ty_rec k (tsubst s U) (tsubst s T).
Proof.
  induction T; intros s k U Hlc; simpl.
  - (* BVar *) destruct (Nat.eqb k n) eqn:E; reflexivity.
  - (* FVar *) f_equal. symmetry.
    replace k with (k + 0) by lia.
    apply open_ty_rec_closed. apply Hlc.
  - (* Arrow *) rewrite IHT1, IHT2; auto.
  - (* All *) rewrite IHT; auto.
Qed.

Lemma tsubst_wf_gen : forall Delta T,
  wf_ty Delta T ->
  forall Delta' s,
    (forall X, lc_ty_at 0 (s X)) ->
    (forall X, In X Delta -> wf_ty Delta' (s X)) ->
    wf_ty Delta' (tsubst s T).
Proof.
  intros Delta T H. induction H; intros Delta' s Hlc Hwf; simpl.
  - apply Hwf. assumption.
  - apply WF_Arrow; auto.
  - (* WF_All *)
    apply WF_All with (L := L ++ fv_ty T).
    intros Y HY.
    assert (HYL : ~ In Y L).
    { intro Hin. apply HY. apply in_app_iff. left. assumption. }
    assert (HYfv : ~ In Y (fv_ty T)).
    { intro Hin. apply HY. apply in_app_iff. right. assumption. }
    set (s' := tvar_update s Y (Ty_FVar Y)).
    assert (Hs'lc : forall X, lc_ty_at 0 (s' X)).
    { intros X. unfold s', tvar_update. simpl. destruct (Nat.eqb X Y) eqn:E.
      - apply lc_ty_fvar.
      - apply Hlc. }
    assert (Hs'wf : forall X, In X (Y :: Delta) -> wf_ty (Y :: Delta') (s' X)).
    { intros X HX. simpl in HX. destruct HX as [-> | HX].
      - unfold s', tvar_update. simpl. rewrite Nat.eqb_refl. apply WF_Var. simpl. left. reflexivity.
      - unfold s', tvar_update. simpl. destruct (Nat.eqb X Y) eqn:E.
        + apply WF_Var. simpl. left. reflexivity.
        + apply wf_ty_weaken. apply Hwf. assumption. }
    specialize (H0 Y HYL (Y :: Delta') s' Hs'lc Hs'wf).
    change (wf_ty (Y :: Delta') (tsubst s' (open_ty_rec 0 (Ty_FVar Y) T))) in H0.
    rewrite tsubst_open_ty_rec in H0 by assumption.
    replace (tsubst s' (Ty_FVar Y)) with (Ty_FVar Y) in H0.
    2: { unfold s', tvar_update. simpl. rewrite Nat.eqb_refl. reflexivity. }
    replace (tsubst s' T) with (tsubst s T) in H0.
    2: { apply tsubst_agree. intros X HX. unfold s', tvar_update. simpl.
         destruct (Nat.eqb X Y) eqn:E.
         - apply Nat.eqb_eq in E. subst. contradiction.
         - reflexivity. }
    exact H0.
Qed.

Lemma tsubst_wf : forall Delta T s,
  wf_ty Delta T ->
  (forall X, lc_ty_at 0 (s X)) ->
  (forall X, In X Delta -> wf_ty [] (s X)) ->
  wf_ty [] (tsubst s T).
Proof.
  intros. apply tsubst_wf_gen with (Delta := Delta) (Delta' := []); auto.
Qed.

Lemma tsubst_lc : forall T K s,
  lc_ty_at K T ->
  (forall X, lc_ty_at K (s X)) ->
  lc_ty_at K (tsubst s T).
Proof.
  induction T; intros K s Hlc Hs; simpl.
  - assumption.
  - apply Hs.
  - inversion Hlc; subst. apply lc_ty_arrow; auto.
  - inversion Hlc; subst. apply lc_ty_all. apply IHT; auto.
    intros X. exact (lc_ty_at_mono (s X) K (S K) ltac:(lia) (Hs X)).
Qed.

(* Agreement of term+type substitutions on annotations *)
Lemma subst_all_ann_agree : forall t st st' s,
  (forall X, In X (fv_tm_ann t) -> st X = st' X) ->
  subst_all st s t = subst_all st' s t.
Proof.
  induction t; intros st st' s Hagree; simpl.
  - reflexivity.
  - reflexivity.
  - (* abs *) f_equal.
    + apply tsubst_agree. intros X HX. apply Hagree.
      simpl. apply in_app_iff. left. assumption.
    + apply IHt. intros X HX. apply Hagree.
      simpl. apply in_app_iff. right. assumption.
  - (* app *) f_equal.
    + apply IHt1. intros X HX. apply Hagree.
      simpl. apply in_app_iff. left. assumption.
    + apply IHt2. intros X HX. apply Hagree.
      simpl. apply in_app_iff. right. assumption.
  - (* tabs *) f_equal. apply IHt. intros X HX. apply Hagree. exact HX.
  - (* tapp *) f_equal.
    + apply IHt. intros X HX. apply Hagree.
      simpl. apply in_app_iff. left. assumption.
    + apply tsubst_agree. intros X HX. apply Hagree.
      simpl. apply in_app_iff. right. assumption.
  - (* choice *) f_equal.
    + apply IHt1. intros X HX. apply Hagree.
      simpl. apply in_app_iff. left. assumption.
    + apply IHt2. intros X HX. apply Hagree.
      simpl. apply in_app_iff. right. assumption.
Qed.

(* Inert opening of locally closed terms *)
Lemma open_tm_rec_closed : forall t K d,
  lc_tm_at K d t -> forall k u, open_tm_rec (k + d) u t = t.
Proof.
  induction t; intros K d Hlc k u; simpl.
  - (* bvar *) inversion Hlc; subst. destruct (Nat.eqb (k + d) n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - reflexivity.
  - (* abs *) inversion Hlc; subst. f_equal.
    replace (S (k + d)) with (k + S d) by lia.
    exact (IHt K (S d) ltac:(eassumption) k u).
  - (* app *) inversion Hlc; subst. f_equal.
    + exact (IHt1 K d ltac:(eassumption) k u).
    + exact (IHt2 K d ltac:(eassumption) k u).
  - (* tabs *) inversion Hlc; subst. f_equal.
    exact (IHt (S K) d ltac:(eassumption) k u).
  - (* tapp *) inversion Hlc; subst. f_equal.
    exact (IHt K d ltac:(eassumption) k u).
  - (* choice *) inversion Hlc; subst. f_equal.
    + exact (IHt1 K d ltac:(eassumption) k u).
    + exact (IHt2 K d ltac:(eassumption) k u).
Qed.

Lemma open_tm_ty_rec_closed : forall t K d,
  lc_tm_at K d t -> forall k U, open_tm_ty_rec (k + K) U t = t.
Proof.
  induction t; intros K d Hlc k U; simpl.
  - reflexivity.
  - reflexivity.
  - (* abs *) inversion Hlc; subst. f_equal.
    + apply open_ty_rec_closed. eassumption.
    + exact (IHt K (S d) ltac:(eassumption) k U).
  - (* app *) inversion Hlc; subst. f_equal.
    + exact (IHt1 K d ltac:(eassumption) k U).
    + exact (IHt2 K d ltac:(eassumption) k U).
  - (* tabs *) inversion Hlc; subst. f_equal.
    replace (S (k + K)) with (k + S K) by lia.
    exact (IHt (S K) d ltac:(eassumption) k U).
  - (* tapp *) inversion Hlc; subst. f_equal.
    + exact (IHt K d ltac:(eassumption) k U).
    + apply open_ty_rec_closed. eassumption.
  - (* choice *) inversion Hlc; subst. f_equal.
    + exact (IHt1 K d ltac:(eassumption) k U).
    + exact (IHt2 K d ltac:(eassumption) k U).
Qed.

(* Commutation of substitution with term opening *)
Lemma subst_all_open_tm_rec : forall t st s k u,
  (forall x, locally_closed_tm (s x)) ->
  locally_closed_tm u ->
  subst_all st s (open_tm_rec k u t) =
  open_tm_rec k (subst_all st s u) (subst_all st s t).
Proof.
  induction t; intros st s k u Hs Hu; simpl.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E; reflexivity.
  - (* fvar *) simpl. symmetry.
    replace k with (k + 0) by lia.
    exact (open_tm_rec_closed (s a) 0 0 (Hs a) k (subst_all st s u)).
  - (* abs *) f_equal. apply IHt; auto.
  - (* app *) f_equal; auto.
  - (* tabs *) f_equal. apply IHt; auto.
  - (* tapp *) f_equal; auto.
  - (* choice *) f_equal; auto.
Qed.

(* Commutation of substitution with type opening inside a term *)
Lemma subst_all_open_tm_ty_rec : forall t st s k U,
  (forall x, locally_closed_tm (s x)) ->
  (forall X, lc_ty_at 0 (st X)) ->
  subst_all st s (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (tsubst st U) (subst_all st s t).
Proof.
  induction t; intros st s k U Hs Hst; simpl.
  - reflexivity.
  - (* fvar *) symmetry.
    replace k with (k + 0) by lia.
    exact (open_tm_ty_rec_closed (s a) 0 0 (Hs a) k (tsubst st U)).
  - (* abs *) f_equal.
    + apply tsubst_open_ty_rec; auto.
    + apply IHt; auto.
  - (* app *) f_equal; auto.
  - (* tabs *) f_equal. apply IHt; auto.
  - (* tapp *) f_equal.
    + apply IHt; auto.
    + apply tsubst_open_ty_rec; auto.
  - (* choice *) f_equal; auto.
Qed.

Lemma subst_all_id : forall t,
  subst_all (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply tsubst_identity.
    + assumption.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal.
    + assumption.
    + apply tsubst_identity.
  - f_equal; assumption.
Qed.


(* ============================================================ *)
(* Multi-step reduction lemmas                                   *)
(* ============================================================ *)

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H1 H2. induction H1.
  - assumption.
  - eapply multi_step; eauto.
Qed.

Lemma multi_app_l : forall e1 e1' e2,
  locally_closed_tm e2 -> e1 -->* e1' -> tm_app e1 e2 -->* tm_app e1' e2.
Proof.
  intros e1 e1' e2 Hlc H. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + eapply ST_App1; eauto.
    + assumption.
Qed.

Lemma multi_app_r : forall v e2 e2',
  value v -> e2 -->* e2' -> tm_app v e2 -->* tm_app v e2'.
Proof.
  intros v e2 e2' Hv H. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + eapply ST_App2; eauto.
    + assumption.
Qed.

Lemma multi_tapp : forall e e' U,
  locally_closed_ty U -> e -->* e' -> tm_tapp e U -->* tm_tapp e' U.
Proof.
  intros e e' U Hlc H. induction H.
  - apply multi_refl.
  - eapply multi_step.
    + eapply ST_TApp; eauto.
    + assumption.
Qed.

(* ============================================================ *)
(* Logical relation                                              *)
(* ============================================================ *)

Definition SemPred := tm -> Prop.
Definition BEnv := nat -> SemPred.
Definition FEnv := atom -> SemPred.

Definition bshift (Sp : SemPred) (xi : BEnv) : BEnv :=
  fun i => match i with
           | 0 => Sp
           | S j => xi j
           end.

Definition bupd (k : nat) (W : SemPred) (xi : BEnv) : BEnv :=
  fun i => if Nat.eqb i k then W else xi i.

Lemma bupd_eq : forall k W xi v,
  bupd k W xi k v <-> W v.
Proof.
  intros k W xi v.
  change ((if Nat.eqb k k then W else xi k) v <-> W v).
  destruct (Nat.eqb k k) eqn:E.
  - tauto.
  - apply Nat.eqb_neq in E. exfalso. apply E. reflexivity.
Qed.

Lemma bupd_neq : forall k W xi i,
  i <> k -> forall v, bupd k W xi i v <-> xi i v.
Proof.
  intros k W xi i Hneq v.
  change ((if Nat.eqb i k then W else xi i) v <-> xi i v).
  destruct (Nat.eqb i k) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - tauto.
Qed.

Lemma bupd_bshift_agree : forall k W Sp xi i v,
  bupd (S k) W (bshift Sp xi) i v <-> bshift Sp (bupd k W xi) i v.
Proof.
  intros. destruct i; simpl.
  - change ((if Nat.eqb 0 (S k) then W else Sp) v <-> Sp v).
    simpl. tauto.
  - change ((if Nat.eqb (S i) (S k) then W else xi i) v <->
            (if Nat.eqb i k then W else xi i) v).
    simpl. tauto.
Qed.

Fixpoint V (xi : BEnv) (rho : FEnv) (T : ty) (v : tm) {struct T} : Prop :=
  match T with
  | Ty_BVar i => xi i v
  | Ty_FVar X => rho X v
  | Ty_Arrow T1 T2 =>
      forall a, value a -> V xi rho T1 a ->
        exists w, tm_app v a -->* w /\ value w /\ V xi rho T2 w
  | Ty_All Tb =>
      forall U, wf_ty [] U -> forall Sp,
        exists w, tm_tapp v U -->* w /\ value w /\ V (bshift Sp xi) rho Tb w
  end.

Definition R (xi : BEnv) (rho : FEnv) (T : ty) (e : tm) : Prop :=
  exists w, e -->* w /\ value w /\ V xi rho T w.

Lemma R_multi : forall xi rho T e e',
  e -->* e' -> R xi rho T e' -> R xi rho T e.
Proof.
  intros xi rho T e e' Hm [w [Hw [Hv HV]]].
  exists w. split.
  - eapply multi_trans; eauto.
  - split; auto.
Qed.

Lemma R_step : forall xi rho T e e',
  e --> e' -> R xi rho T e' -> R xi rho T e.
Proof.
  intros. eapply R_multi.
  - eapply multi_step; [eassumption | apply multi_refl].
  - assumption.
Qed.

(* Environment extensionality for bound type variables *)
Lemma V_env_ext : forall T xi xi' rho,
  (forall i v, xi i v <-> xi' i v) ->
  forall v, V xi rho T v <-> V xi' rho T v.
Proof.
  induction T; intros xi xi' rho Hagree v; simpl in *.
  - apply Hagree.
  - tauto.
  - (* Arrow *) split; intros HV a Hva HVa.
    + destruct (HV a Hva (proj2 (IHT1 xi xi' rho Hagree a) HVa))
        as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj1 (IHT2 xi xi' rho Hagree w)); auto.
    + destruct (HV a Hva (proj1 (IHT1 xi xi' rho Hagree a) HVa))
        as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj2 (IHT2 xi xi' rho Hagree w)); auto.
  - (* All *) split; intros HV U HU Sp.
    + assert (Hbs : forall i vv, bshift Sp xi i vv <-> bshift Sp xi' i vv).
      { intros i vv. destruct i; simpl.
        - tauto.
        - apply Hagree. }
      destruct (HV U HU Sp) as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj1 (IHT (bshift Sp xi) (bshift Sp xi') rho Hbs w)); auto.
    + assert (Hbs : forall i vv, bshift Sp xi i vv <-> bshift Sp xi' i vv).
      { intros i vv. destruct i; simpl.
        - tauto.
        - apply Hagree. }
      destruct (HV U HU Sp) as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj2 (IHT (bshift Sp xi) (bshift Sp xi') rho Hbs w)); auto.
Qed.

Lemma V_env_agree : forall T d xi xi' rho,
  lc_ty_at d T ->
  (forall i, i < d -> forall v, xi i v <-> xi' i v) ->
  forall v, V xi rho T v <-> V xi' rho T v.
Proof.
  induction T; intros d xi xi' rho Hlc Hagree v; simpl in *.
  - (* BVar *) inversion Hlc; subst. apply Hagree. assumption.
  - tauto.
  - (* Arrow *) inversion Hlc as [k i Hi | k X | k A B H1 H2 | k Tb H1]; subst.
    split; intros HV a Hva HVa.
    + destruct (HV a Hva (proj2 (IHT1 d xi xi' rho H1 Hagree a) HVa))
        as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj1 (IHT2 d xi xi' rho H2 Hagree w)); auto.
    + destruct (HV a Hva (proj1 (IHT1 d xi xi' rho H1 Hagree a) HVa))
        as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj2 (IHT2 d xi xi' rho H2 Hagree w)); auto.
  - (* All *) inversion Hlc as [k i Hi | k X | k A B H1 H2 | k Tb H1]; subst.
    split; intros HV U HU Sp.
    + assert (Hbs : forall i, i < S d -> forall vv,
                 bshift Sp xi i vv <-> bshift Sp xi' i vv).
      { intros i Hi vv. destruct i; simpl.
        - tauto.
        - apply Hagree. lia. }
      destruct (HV U HU Sp) as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj1 (IHT (S d) (bshift Sp xi) (bshift Sp xi') rho H1 Hbs w)); auto.
    + assert (Hbs : forall i, i < S d -> forall vv,
                 bshift Sp xi i vv <-> bshift Sp xi' i vv).
      { intros i Hi vv. destruct i; simpl.
        - tauto.
        - apply Hagree. lia. }
      destruct (HV U HU Sp) as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj2 (IHT (S d) (bshift Sp xi) (bshift Sp xi') rho H1 Hbs w)); auto.
Qed.

Lemma V_env_indep : forall T xi xi' rho,
  lc_ty_at 0 T ->
  forall v, V xi rho T v <-> V xi' rho T v.
Proof.
  intros. apply V_env_agree with (d := 0); auto. intros i Hi. lia.
Qed.

(* Agreement for free type variable environments *)
Lemma V_rho_agree : forall T xi rho rho',
  (forall X, In X (fv_ty T) -> forall v, rho X v <-> rho' X v) ->
  forall v, V xi rho T v <-> V xi rho' T v.
Proof.
  induction T; intros xi rho rho' Hagree v; simpl in *.
  - (* BVar *) tauto.
  - (* FVar *) apply Hagree. simpl. left. reflexivity.
  - (* Arrow *)
    assert (H1 : forall X, In X (fv_ty T1) -> forall vv, rho X vv <-> rho' X vv).
    { intros X HX vv. apply Hagree. simpl.
      apply in_app_iff. left. assumption. }
    assert (H2 : forall X, In X (fv_ty T2) -> forall vv, rho X vv <-> rho' X vv).
    { intros X HX vv. apply Hagree. simpl.
      apply in_app_iff. right. assumption. }
    split; intros HV a Hva HVa.
    + destruct (HV a Hva (proj2 (IHT1 xi rho rho' H1 a) HVa))
        as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj1 (IHT2 xi rho rho' H2 w)); auto.
    + destruct (HV a Hva (proj1 (IHT1 xi rho rho' H1 a) HVa))
        as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj2 (IHT2 xi rho rho' H2 w)); auto.
  - (* All *)
    assert (Htb : forall X, In X (fv_ty T) -> forall vv, rho X vv <-> rho' X vv).
    { intros X HX vv. apply Hagree. simpl. assumption. }
    split; intros HV U HU Sp.
    + destruct (HV U HU Sp) as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj1 (IHT (bshift Sp xi) rho rho' Htb w)); auto.
    + destruct (HV U HU Sp) as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj2 (IHT (bshift Sp xi) rho rho' Htb w)); auto.
Qed.

(* Agreement of b-updated and shifted environments *)
Lemma bupd_bshift_agree2 : forall k W W' Sp xi i v,
  (forall w, W w <-> W' w) ->
  bupd (S k) W (bshift Sp xi) i v <-> bshift Sp (bupd k W' xi) i v.
Proof.
  intros k W W' Sp xi i v HW. destruct i; simpl.
  - change ((if Nat.eqb 0 (S k) then W else Sp) v <-> Sp v).
    simpl. tauto.
  - change ((if Nat.eqb i k then W else xi i) v <->
            (if Nat.eqb i k then W' else xi i) v).
    destruct (Nat.eqb i k).
    + apply HW.
    + tauto.
Qed.

(* Opening lemma for the type semantics *)
Lemma V_open_ty_gen : forall T k xi rho U,
  lc_ty_at 0 U ->
  forall v,
    V xi rho (open_ty_rec k U T) v <->
    V (bupd k (fun w => V xi rho U w) xi) rho T v.
Proof.
  induction T; intros k xi rho U HU v; simpl.
  - (* BVar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply iff_sym. apply bupd_eq.
    + apply Nat.eqb_neq in E. apply iff_sym. apply bupd_neq. lia.
  - (* FVar *) tauto.
  - (* Arrow *) split; intros HV a Hva HVa.
    + destruct (HV a Hva (proj2 (IHT1 k xi rho U HU a) HVa))
        as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj1 (IHT2 k xi rho U HU w)); auto.
    + destruct (HV a Hva (proj1 (IHT1 k xi rho U HU a) HVa))
        as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj2 (IHT2 k xi rho U HU w)); auto.
  - (* All *) split; intros HV U' HU' Sp.
    + assert (HWeq : forall w0,
          V (bshift Sp xi) rho U w0 <-> V xi rho U w0).
      { intros w0. apply iff_sym. apply V_env_indep; auto. }
      assert (Hbs : forall i vv,
          bupd (S k) (fun w0 => V (bshift Sp xi) rho U w0) (bshift Sp xi) i vv <->
          bshift Sp (bupd k (fun w0 => V xi rho U w0) xi) i vv).
      { intros i vv. apply bupd_bshift_agree2. intros w0. apply HWeq. }
      destruct (HV U' HU' Sp) as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj1 (V_env_ext _
        (bupd (S k) (fun w0 => V (bshift Sp xi) rho U w0) (bshift Sp xi))
        (bshift Sp (bupd k (fun w0 => V xi rho U w0) xi)) rho Hbs w)).
      apply (proj1 (IHT (S k) (bshift Sp xi) rho U HU w)).
      exact HVw.
    + assert (HWeq : forall w0,
          V (bshift Sp xi) rho U w0 <-> V xi rho U w0).
      { intros w0. apply iff_sym. apply V_env_indep; auto. }
      assert (Hbs : forall i vv,
          bupd (S k) (fun w0 => V (bshift Sp xi) rho U w0) (bshift Sp xi) i vv <->
          bshift Sp (bupd k (fun w0 => V xi rho U w0) xi) i vv).
      { intros i vv. apply bupd_bshift_agree2. intros w0. apply HWeq. }
      destruct (HV U' HU' Sp) as [w [Hm [Hw HVw]]].
      exists w. split; auto. split; auto.
      apply (proj2 (IHT (S k) (bshift Sp xi) rho U HU w)).
      apply (proj2 (V_env_ext _
        (bupd (S k) (fun w0 => V (bshift Sp xi) rho U w0) (bshift Sp xi))
        (bshift Sp (bupd k (fun w0 => V xi rho U w0) xi)) rho Hbs w)).
      exact HVw.
Qed.

Lemma V_open_ty : forall T xi rho U,
  lc_ty_at 0 U ->
  forall v,
    V xi rho (open_ty T U) v <->
    V (bshift (fun w => V xi rho U w) xi) rho T v.
Proof.
  intros T xi rho U HU v.
  transitivity (V (bupd 0 (fun w => V xi rho U w) xi) rho T v).
  - change (V xi rho (open_ty_rec 0 U T) v <->
            V (bupd 0 (fun w => V xi rho U w) xi) rho T v).
    apply V_open_ty_gen; auto.
  - apply V_env_ext. intros i vv. destruct i; simpl.
    + apply bupd_eq.
    + apply bupd_neq. lia.
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

End SystemFParametricityNondeterminismHardTask.
