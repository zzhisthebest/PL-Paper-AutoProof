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

(* ================================================================= *)
(* Auxiliary infrastructure for the logical relation.                *)
(* ================================================================= *)

(* ----------------------------------------------------------------- *)
(* Size, free atoms, free term variables                              *)
(* ----------------------------------------------------------------- *)

Fixpoint size_ty (T : ty) : nat :=
  match T with
  | Ty_BVar _ => 1
  | Ty_FVar _ => 1
  | Ty_Arrow T1 T2 => S (size_ty T1 + size_ty T2)
  | Ty_All T1 => S (size_ty T1)
  end.

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
  | tm_fvar _ => []
  | tm_abs T b => atoms_ty T ++ atoms_tm b
  | tm_app a b => atoms_tm a ++ atoms_tm b
  | tm_tabs b => atoms_tm b
  | tm_tapp a T => atoms_tm a ++ atoms_ty T
  | tm_choice a b => atoms_tm a ++ atoms_tm b
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T b => fv_tm b
  | tm_app a b => fv_tm a ++ fv_tm b
  | tm_tabs b => fv_tm b
  | tm_tapp a T => fv_tm a
  | tm_choice a b => fv_tm a ++ fv_tm b
  end.

Definition ctx_atoms (Gamma : context) : list atom :=
  flat_map (fun p => atoms_ty (snd p)) Gamma.

Definition ctx_vars (Gamma : context) : list atom := map fst Gamma.

Definition fresh_atom (l : list atom) : atom := fold_right max 0 l + 1.

Lemma fresh_atom_notin : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l. unfold fresh_atom.
  assert (H : forall a, In a l -> a <= fold_right max 0 l).
  { induction l as [| b l IH]; intros a Ha.
    - inversion Ha.
    - simpl in *. destruct Ha as [-> | Ha].
      + lia.
      + specialize (IH a Ha); lia. }
  intros Hin. specialize (H (fold_right max 0 l + 1) Hin). lia.
Qed.

Lemma notin_app_iff : forall (l1 l2 : list atom) x,
  ~ In x (l1 ++ l2) <-> ~ In x l1 /\ ~ In x l2.
Proof.
  intros. rewrite in_app_iff. tauto.
Qed.

(* ----------------------------------------------------------------- *)
(* Type / term substitution for atoms and term variables              *)
(* ----------------------------------------------------------------- *)

Fixpoint tysub (sig : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sig X
  | Ty_Arrow T1 T2 => Ty_Arrow (tysub sig T1) (tysub sig T2)
  | Ty_All T1 => Ty_All (tysub sig T1)
  end.

Fixpoint tmsubst_ty (sig : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (tysub sig T) (tmsubst_ty sig b)
  | tm_app a b => tm_app (tmsubst_ty sig a) (tmsubst_ty sig b)
  | tm_tabs b => tm_tabs (tmsubst_ty sig b)
  | tm_tapp a T => tm_tapp (tmsubst_ty sig a) (tysub sig T)
  | tm_choice a b => tm_choice (tmsubst_ty sig a) (tmsubst_ty sig b)
  end.

Fixpoint tmsubst_fv (gam : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gam x
  | tm_abs T b => tm_abs T (tmsubst_fv gam b)
  | tm_app a b => tm_app (tmsubst_fv gam a) (tmsubst_fv gam b)
  | tm_tabs b => tm_tabs (tmsubst_fv gam b)
  | tm_tapp a T => tm_tapp (tmsubst_fv gam a) T
  | tm_choice a b => tm_choice (tmsubst_fv gam a) (tmsubst_fv gam b)
  end.

Definition pty (sig : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb Y X then U else sig Y.

Definition pfv (gam : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then v else gam y.

Definition idty (X : atom) : ty := Ty_FVar X.

Lemma pty_same : forall sig X U, pty sig X U X = U.
Proof. intros. unfold pty. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma pty_other : forall sig X U Y, Y <> X -> pty sig X U Y = sig Y.
Proof. intros. unfold pty. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma pfv_same : forall gam x v, pfv gam x v x = v.
Proof. intros. unfold pfv. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma pfv_other : forall gam x v y, y <> x -> pfv gam x v y = gam y.
Proof. intros. unfold pfv. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

(* Membership facts for the syntactic helper functions *)

Lemma In_atoms_ty_open : forall X k U T,
  In X (atoms_ty (open_ty_rec k U T)) -> In X (atoms_ty T) \/ In X (atoms_ty U).
Proof.
  intros X k U T. revert k. induction T; intros k H; simpl in *.
  - destruct (Nat.eqb k n); simpl in *.
    + right. exact H.
    + destruct H.
  - simpl in *. left. exact H.
  - apply in_app_iff in H. destruct H as [H | H].
    + apply IHT1 in H. destruct H as [H | H].
      * left. apply in_app_iff. left. exact H.
      * right. exact H.
    + apply IHT2 in H. destruct H as [H | H].
      * left. apply in_app_iff. right. exact H.
      * right. exact H.
  - apply IHT in H. exact H.
Qed.

Lemma In_atoms_tm_open_ty : forall X k U t,
  In X (atoms_tm (open_tm_ty_rec k U t)) -> In X (atoms_tm t) \/ In X (atoms_ty U).
Proof.
  intros X k U t. revert k. induction t; intros k H; simpl in *.
  - destruct H.
  - destruct H.
  - apply in_app_iff in H. destruct H as [H | H].
    + apply In_atoms_ty_open in H. destruct H as [H | H]; [left; apply in_app_iff; left | right]; auto.
    + apply IHt in H. destruct H as [H | H]; [left; apply in_app_iff; right | right]; auto.
  - apply in_app_iff in H. destruct H as [H | H].
    + apply IHt1 in H. destruct H as [H | H]; [left; apply in_app_iff; left | right]; auto.
    + apply IHt2 in H. destruct H as [H | H]; [left; apply in_app_iff; right | right]; auto.
  - apply IHt in H. destruct H as [H | H]; [left | right]; auto.
  - apply in_app_iff in H. destruct H as [H | H].
    + apply IHt in H. destruct H as [H | H]; [left; apply in_app_iff; left | right]; auto.
    + apply In_atoms_ty_open in H. destruct H as [H | H]; [left; apply in_app_iff; right | right]; auto.
  - apply in_app_iff in H. destruct H as [H | H].
    + apply IHt1 in H. destruct H as [H | H]; [left; apply in_app_iff; left | right]; auto.
    + apply IHt2 in H. destruct H as [H | H]; [left; apply in_app_iff; right | right]; auto.
Qed.

Lemma In_atoms_ty_tysub : forall X sig T,
  In X (atoms_ty (tysub sig T)) <->
  exists Y, In Y (atoms_ty T) /\ In X (atoms_ty (sig Y)).
Proof.
  intros X sig T. induction T; simpl.
  - split; [intros [] | intros [Y [HY _]]; inversion HY].
  - split.
    + intros H. exists a. split; [left; reflexivity | exact H].
    + intros [Y [HY HX]]. destruct HY as [-> | []]; exact HX.
  - split.
    + intros H. apply in_app_iff in H. destruct H as [H | H].
      * apply IHT1 in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. left. exact HY.
        -- exact HX.
      * apply IHT2 in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. right. exact HY.
        -- exact HX.
    + intros [Y [HY HX]]. apply in_app_iff in HY. destruct HY as [HY | HY].
      * apply in_app_iff. left. apply IHT1. exists Y. split; auto.
      * apply in_app_iff. right. apply IHT2. exists Y. split; auto.
  - apply IHT.
Qed.

Lemma In_atoms_tm_tmsubst_ty : forall X sig t,
  In X (atoms_tm (tmsubst_ty sig t)) <->
  exists Y, In Y (atoms_tm t) /\ In X (atoms_ty (sig Y)).
Proof.
  intros X sig t. induction t; simpl.
  - split; [intros [] | intros [Y [HY _]]; inversion HY].
  - split; [intros [] | intros [Y [HY _]]; inversion HY].
  - (* abs *) split.
    + intros H. apply in_app_iff in H. destruct H as [H | H].
      * apply In_atoms_ty_tysub in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. left. exact HY.
        -- exact HX.
      * apply IHt in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. right. exact HY.
        -- exact HX.
    + intros [Y [HY HX]]. apply in_app_iff in HY. destruct HY as [HY | HY].
      * apply in_app_iff. left. apply In_atoms_ty_tysub. exists Y. split; auto.
      * apply in_app_iff. right. apply IHt. exists Y. split; auto.
  - (* app *) split.
    + intros H. apply in_app_iff in H. destruct H as [H | H].
      * apply IHt1 in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. left. exact HY.
        -- exact HX.
      * apply IHt2 in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. right. exact HY.
        -- exact HX.
    + intros [Y [HY HX]]. apply in_app_iff in HY. destruct HY as [HY | HY].
      * apply in_app_iff. left. apply IHt1. exists Y. split; auto.
      * apply in_app_iff. right. apply IHt2. exists Y. split; auto.
  - (* tabs *) apply IHt.
  - (* tapp *) split.
    + intros H. apply in_app_iff in H. destruct H as [H | H].
      * apply IHt in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. left. exact HY.
        -- exact HX.
      * apply In_atoms_ty_tysub in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. right. exact HY.
        -- exact HX.
    + intros [Y [HY HX]]. apply in_app_iff in HY. destruct HY as [HY | HY].
      * apply in_app_iff. left. apply IHt. exists Y. split; auto.
      * apply in_app_iff. right. apply In_atoms_ty_tysub. exists Y. split; auto.
  - (* choice *) split.
    + intros H. apply in_app_iff in H. destruct H as [H | H].
      * apply IHt1 in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. left. exact HY.
        -- exact HX.
      * apply IHt2 in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. right. exact HY.
        -- exact HX.
    + intros [Y [HY HX]]. apply in_app_iff in HY. destruct HY as [HY | HY].
      * apply in_app_iff. left. apply IHt1. exists Y. split; auto.
      * apply in_app_iff. right. apply IHt2. exists Y. split; auto.
Qed.

Lemma In_fv_tm_open_fwd : forall X k u t,
  In X (fv_tm t) -> In X (fv_tm (open_tm_rec k u t)).
Proof.
  intros X k u t. revert k. induction t; intros k H; simpl in *.
  - destruct H.
  - auto.
  - apply IHt; auto.
  - apply in_app_iff in H. destruct H as [H | H]; apply in_app_iff.
    + left. apply IHt1; auto.
    + right. apply IHt2; auto.
  - apply IHt; auto.
  - apply IHt; auto.
  - apply in_app_iff in H. destruct H as [H | H]; apply in_app_iff.
    + left. apply IHt1; auto.
    + right. apply IHt2; auto.
Qed.

Lemma In_fv_tm_ty_open : forall X k U t,
  In X (fv_tm (open_tm_ty_rec k U t)) <-> In X (fv_tm t).
Proof.
  intros X k U t. revert k. induction t; intros k; simpl.
  - tauto.
  - tauto.
  - apply IHt.
  - split; intros H.
    + apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply (proj1 (IHt1 k)); auto.
      * apply in_app_iff. right. apply (proj1 (IHt2 k)); auto.
    + apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply (proj2 (IHt1 k)); auto.
      * apply in_app_iff. right. apply (proj2 (IHt2 k)); auto.
  - apply IHt.
  - apply IHt.
  - split; intros H.
    + apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply (proj1 (IHt1 k)); auto.
      * apply in_app_iff. right. apply (proj1 (IHt2 k)); auto.
    + apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply (proj2 (IHt1 k)); auto.
      * apply in_app_iff. right. apply (proj2 (IHt2 k)); auto.
Qed.

Lemma In_fv_tm_tmsubst_ty : forall X sig t,
  In X (fv_tm (tmsubst_ty sig t)) <-> In X (fv_tm t).
Proof.
  intros X sig t. induction t; simpl.
  - tauto.
  - tauto.
  - apply IHt.
  - split; intros H.
    + apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply (proj1 IHt1); auto.
      * apply in_app_iff. right. apply (proj1 IHt2); auto.
    + apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply (proj2 IHt1); auto.
      * apply in_app_iff. right. apply (proj2 IHt2); auto.
  - apply IHt.
  - apply IHt.
  - split; intros H.
    + apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply (proj1 IHt1); auto.
      * apply in_app_iff. right. apply (proj1 IHt2); auto.
    + apply in_app_iff in H. destruct H as [H | H].
      * apply in_app_iff. left. apply (proj2 IHt1); auto.
      * apply in_app_iff. right. apply (proj2 IHt2); auto.
Qed.

Lemma In_fv_tm_tmsubst_fv : forall X gam t,
  In X (fv_tm (tmsubst_fv gam t)) <->
  exists Y, In Y (fv_tm t) /\ In X (fv_tm (gam Y)).
Proof.
  intros X gam t. induction t; simpl.
  - split; intros H; [inversion H | destruct H as [Y [HY _]]; inversion HY].
  - split; intros H; [exists a; tauto | destruct H as [Y [HY HX]]; simpl in HY; destruct HY as [-> | []]; exact HX].
  - apply IHt.
  - split.
    + intros H. apply in_app_iff in H. destruct H as [H | H].
      * apply (proj1 IHt1) in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. left. exact HY.
        -- exact HX.
      * apply (proj1 IHt2) in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. right. exact HY.
        -- exact HX.
    + intros [Y [HY HX]]. apply in_app_iff in HY. destruct HY as [HY | HY].
      * apply in_app_iff. left. apply (proj2 IHt1). exists Y. split; auto.
      * apply in_app_iff. right. apply (proj2 IHt2). exists Y. split; auto.
  - apply IHt.
  - apply IHt.
  - split.
    + intros H. apply in_app_iff in H. destruct H as [H | H].
      * apply (proj1 IHt1) in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. left. exact HY.
        -- exact HX.
      * apply (proj1 IHt2) in H. destruct H as [Y [HY HX]]. exists Y. split.
        -- apply in_app_iff. right. exact HY.
        -- exact HX.
    + intros [Y [HY HX]]. apply in_app_iff in HY. destruct HY as [HY | HY].
      * apply in_app_iff. left. apply (proj2 IHt1). exists Y. split; auto.
      * apply in_app_iff. right. apply (proj2 IHt2). exists Y. split; auto.
Qed.

(* Freshness-based irrelevance of point updates *)

Lemma atoms_ty_tysub_irrel : forall sig X U T,
  ~ In X (atoms_ty T) -> tysub (pty sig X U) T = tysub sig T.
Proof.
  intros sig X U T H. induction T; simpl.
  - reflexivity.
  - simpl in H. assert (a <> X) by (intros ->; apply H; simpl; auto).
    apply pty_other; auto.
  - simpl in H. apply notin_app_iff in H. destruct H as [H1 H2].
    rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
Qed.

Lemma atoms_tm_tmsubst_ty_irrel : forall sig X U t,
  ~ In X (atoms_tm t) -> tmsubst_ty (pty sig X U) t = tmsubst_ty sig t.
Proof.
  intros sig X U t H. induction t; simpl in *.
  - reflexivity.
  - reflexivity.
  - apply notin_app_iff in H. destruct H as [H1 H2].
    rewrite atoms_ty_tysub_irrel, IHt; auto.
  - apply notin_app_iff in H. destruct H as [H1 H2].
    rewrite IHt1, IHt2; auto.
  - f_equal. apply IHt; auto.
  - apply notin_app_iff in H. destruct H as [H1 H2].
    rewrite atoms_ty_tysub_irrel, IHt; auto.
  - apply notin_app_iff in H. destruct H as [H1 H2].
    rewrite IHt1, IHt2; auto.
Qed.

Lemma fv_tm_tmsubst_fv_irrel : forall t gam1 gam2,
  (forall x, In x (fv_tm t) -> gam1 x = gam2 x) ->
  tmsubst_fv gam1 t = tmsubst_fv gam2 t.
Proof.
  intros t. induction t; simpl; intros gam1 gam2 H.
  - reflexivity.
  - apply H. simpl. auto.
  - f_equal. apply IHt. intros x Hx. apply H. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. apply in_app_iff. left. exact Hx.
    + apply IHt2. intros x Hx. apply H. apply in_app_iff. right. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. exact Hx.
  - f_equal. apply IHt. intros x Hx. apply H. exact Hx.
  - f_equal.
    + apply IHt1. intros x Hx. apply H. apply in_app_iff. left. exact Hx.
    + apply IHt2. intros x Hx. apply H. apply in_app_iff. right. exact Hx.
Qed.

(* Commutation lemmas *)

Lemma lc_ty_arrow_inv : forall k T1 T2,
  lc_ty_at k (Ty_Arrow T1 T2) -> lc_ty_at k T1 /\ lc_ty_at k T2.
Proof. intros k T1 T2 H. inversion H; subst; auto. Qed.

Lemma lc_ty_bvar_inv : forall k i, lc_ty_at k (Ty_BVar i) -> i < k.
Proof. intros k i H. inversion H; subst; auto. Qed.

Lemma lc_ty_all_inv : forall k T,
  lc_ty_at k (Ty_All T) -> lc_ty_at (S k) T.
Proof. intros k T H. inversion H; subst; auto. Qed.

Lemma lc_ty_at_mono : forall k k' T, lc_ty_at k T -> k <= k' -> lc_ty_at k' T.
Proof.
  intros k k' T H. revert k'. induction H; intros k' Hle.
  - constructor. lia.
  - constructor.
  - constructor; [apply IHlc_ty_at1 | apply IHlc_ty_at2]; auto.
  - constructor. apply IHlc_ty_at. lia.
Qed.

Lemma lc_tm_at_mono : forall K k K' k' t,
  lc_tm_at K k t -> K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros K k K' k' t H. revert K' k'.
  induction H as [ K k i Hlt
                 | K k x
                 | K k T t Hty Hrec IHrec
                 | K k t1 t2 Hrec1 IH1 Hrec2 IH2
                 | K k t Hrec IHrec
                 | K k t T Hrec IHrec Hty
                 | K k t1 t2 Hrec1 IH1 Hrec2 IH2 ];
  intros K' k' HK Hk.
  - constructor. lia.
  - constructor.
  - constructor.
    + apply lc_ty_at_mono with (k := K); [exact Hty | lia].
    + apply IHrec; lia.
  - constructor; [apply IH1; lia | apply IH2; lia].
  - constructor. apply IHrec; lia.
  - constructor.
    + apply IHrec; lia.
    + apply lc_ty_at_mono with (k := K); [exact Hty | lia].
  - constructor; [apply IH1; lia | apply IH2; lia].
Qed.

Lemma open_ty_rec_lc : forall k U T, lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  intros k U T. revert k U. induction T; intros k U H; simpl.
  - destruct (Nat.eqb k n) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E. subst. inversion H. lia.
  - reflexivity.
  - apply lc_ty_arrow_inv in H. destruct H as [H1 H2].
    rewrite (IHT1 k U H1), (IHT2 k U H2). reflexivity.
  - apply lc_ty_all_inv in H.
    rewrite (IHT (S k) U H). reflexivity.
Qed.

Lemma lc_tm_abs_inv : forall K k T b,
  lc_tm_at K k (tm_abs T b) -> lc_ty_at K T /\ lc_tm_at K (S k) b.
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_tm_app_inv : forall K k a b,
  lc_tm_at K k (tm_app a b) -> lc_tm_at K k a /\ lc_tm_at K k b.
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_tm_tabs_inv : forall K k b,
  lc_tm_at K k (tm_tabs b) -> lc_tm_at (S K) k b.
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_tm_tapp_inv : forall K k b T,
  lc_tm_at K k (tm_tapp b T) -> lc_tm_at K k b /\ lc_ty_at K T.
Proof. intros. inversion H; subst; auto. Qed.

Lemma lc_tm_choice_inv : forall K k a b,
  lc_tm_at K k (tm_choice a b) -> lc_tm_at K k a /\ lc_tm_at K k b.
Proof. intros. inversion H; subst; auto. Qed.

Lemma open_tm_rec_lc : forall K j u t, lc_tm_at K j t -> open_tm_rec j u t = t.
Proof.
  intros K j u t. revert K j.
  induction t as [ n | a | T b IH | t1 IH1 t2 IH2 | b IH | a IH T | t1 IH1 t2 IH2 ];
  intros K j H; simpl.
  - destruct (Nat.eqb j n) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E. subst. inversion H. lia.
  - reflexivity.
  - apply lc_tm_abs_inv in H. destruct H as [Hty Hb].
    rewrite (IH K (S j) Hb). reflexivity.
  - apply lc_tm_app_inv in H. destruct H as [H1 H2].
    rewrite (IH1 K j H1), (IH2 K j H2). reflexivity.
  - apply lc_tm_tabs_inv in H. rewrite (IH (S K) j H). reflexivity.
  - apply lc_tm_tapp_inv in H. destruct H as [H1 H2].
    rewrite (IH K j H1). reflexivity.
  - apply lc_tm_choice_inv in H. destruct H as [H1 H2].
    rewrite (IH1 K j H1), (IH2 K j H2). reflexivity.
Qed.

Lemma open_tm_ty_rec_lc : forall K k j U t,
  K <= j -> lc_tm_at K k t -> open_tm_ty_rec j U t = t.
Proof.
  intros K k j U t. revert K k j.
  induction t as [ n | a | T b IH | t1 IH1 t2 IH2 | b IH | a IH T | t1 IH1 t2 IH2 ];
  intros K k j Hle H; simpl.
  - reflexivity.
  - reflexivity.
  - apply lc_tm_abs_inv in H. destruct H as [Hty Hb].
    rewrite (open_ty_rec_lc j U T) by (apply lc_ty_at_mono with (k := K); auto).
    rewrite (IH K (S k) j Hle Hb). reflexivity.
  - apply lc_tm_app_inv in H. destruct H as [H1 H2].
    rewrite (IH1 K k j Hle H1), (IH2 K k j Hle H2). reflexivity.
  - apply lc_tm_tabs_inv in H.
    rewrite (IH (S K) k (S j)); auto. lia.
  - apply lc_tm_tapp_inv in H. destruct H as [H1 H2].
    rewrite (open_ty_rec_lc j U T) by (apply lc_ty_at_mono with (k := K); auto).
    rewrite (IH K k j Hle H1). reflexivity.
  - apply lc_tm_choice_inv in H. destruct H as [H1 H2].
    rewrite (IH1 K k j Hle H1), (IH2 K k j Hle H2). reflexivity.
Qed.

Lemma tysub_open_ty : forall sig, (forall X, lc_ty_at 0 (sig X)) ->
  forall k U T,
  tysub sig (open_ty_rec k U T) = open_ty_rec k (tysub sig U) (tysub sig T).
Proof.
  intros sig Hs k U T. revert k. induction T; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite open_ty_rec_lc. reflexivity.
    apply lc_ty_at_mono with (k := 0); auto. lia.
  - rewrite (IHT1 k), (IHT2 k). reflexivity.
  - rewrite (IHT (S k)). reflexivity.
Qed.

Lemma tmsubst_ty_open_tm : forall sig k u t,
  tmsubst_ty sig (open_tm_rec k u t) =
  open_tm_rec k (tmsubst_ty sig u) (tmsubst_ty sig t).
Proof.
  intros sig k u t. revert k. induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma tmsubst_ty_open_tm_ty : forall sig, (forall X, lc_ty_at 0 (sig X)) ->
  forall k U t,
  tmsubst_ty sig (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (tysub sig U) (tmsubst_ty sig t).
Proof.
  intros sig Hs k U t. revert k.
  induction t as [ n | a | T b IH | t1 IH1 t2 IH2 | b IH | a IH T | t1 IH1 t2 IH2 ];
  intros k; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (tysub_open_ty sig Hs k U T), (IH k). reflexivity.
  - rewrite (IH1 k), (IH2 k). reflexivity.
  - rewrite (IH (S k)). reflexivity.
  - rewrite (tysub_open_ty sig Hs k U T), (IH k). reflexivity.
  - rewrite (IH1 k), (IH2 k). reflexivity.
Qed.

Lemma tmsubst_fv_open_tm : forall gam, (forall x, lc_tm_at 0 0 (gam x)) ->
  forall k u t,
  tmsubst_fv gam (open_tm_rec k u t) =
  open_tm_rec k (tmsubst_fv gam u) (tmsubst_fv gam t).
Proof.
  intros gam Hg k u t. revert k. induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite (open_tm_rec_lc 0 k (tmsubst_fv gam u) (gam a)).
    + reflexivity.
    + apply lc_tm_at_mono with (K := 0) (k := 0); auto; lia.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma tmsubst_fv_open_tm_ty : forall gam, (forall x, lc_tm_at 0 0 (gam x)) ->
  forall k U t,
  tmsubst_fv gam (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (tmsubst_fv gam t).
Proof.
  intros gam Hg k U t. revert k. induction t; intros k; simpl.
  - reflexivity.
  - rewrite (open_tm_ty_rec_lc 0 0 k U (gam a)).
    + reflexivity.
    + lia.
    + apply lc_tm_at_mono with (K := 0) (k := 0); auto; lia.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite (IHt (S k)). reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma tysub_idty : forall T, tysub idty T = T.
Proof.
  intros T. induction T; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
  - rewrite IHT. reflexivity.
Qed.

Lemma tmsubst_ty_idty : forall t, tmsubst_ty idty t = t.
Proof.
  intros t. induction t; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite tysub_idty, IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite tysub_idty, IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

(* Key instantiation lemmas used when passing under binders *)

Lemma tmsubst_ty_point_open : forall sig X U t,
  (forall Y, lc_ty_at 0 (sig Y)) -> lc_ty_at 0 U ->
  ~ In X (atoms_tm t) ->
  tmsubst_ty (pty sig X U) (open_tm_ty_rec 0 (Ty_FVar X) t) =
  open_tm_ty_rec 0 U (tmsubst_ty sig t).
Proof.
  intros sig X U t Hs HU HX.
  assert (Hlc : forall Y, lc_ty_at 0 (pty sig X U Y)).
  { intros Y. unfold pty. destruct (Nat.eqb Y X) eqn:E.
    - apply Nat.eqb_eq in E. subst. exact HU.
    - apply Hs. }
  rewrite (tmsubst_ty_open_tm_ty (pty sig X U) Hlc).
  change (open_tm_ty_rec 0 (pty sig X U X) (tmsubst_ty (pty sig X U) t) =
          open_tm_ty_rec 0 U (tmsubst_ty sig t)).
  rewrite pty_same.
  rewrite atoms_tm_tmsubst_ty_irrel; [reflexivity | exact HX].
Qed.

Lemma tmsubst_fv_point_open : forall gam x v t,
  (forall y, lc_tm_at 0 0 (gam y)) -> lc_tm_at 0 0 v ->
  ~ In x (fv_tm t) ->
  tmsubst_fv (pfv gam x v) (open_tm_rec 0 (tm_fvar x) t) =
  open_tm_rec 0 v (tmsubst_fv gam t).
Proof.
  intros gam x v t Hg Hv H.
  assert (Hg' : forall y, lc_tm_at 0 0 (pfv gam x v y)).
  { intros y. unfold pfv. destruct (Nat.eqb y x) eqn:E.
    - apply Nat.eqb_eq in E. subst. exact Hv.
    - apply Hg. }
  rewrite (tmsubst_fv_open_tm (pfv gam x v) Hg').
  change (open_tm_rec 0 (pfv gam x v x) (tmsubst_fv (pfv gam x v) t) =
          open_tm_rec 0 v (tmsubst_fv gam t)).
  rewrite pfv_same.
  rewrite (fv_tm_tmsubst_fv_irrel t (pfv gam x v) gam); [reflexivity |].
  intros y Hy. apply pfv_other. intros ->. apply H. exact Hy.
Qed.

(* ----------------------------------------------------------------- *)
(* Locally closed: monotonicity, opening, substitution                *)
(* ----------------------------------------------------------------- *)

Lemma lc_ty_open_inv : forall j U T,
  lc_ty_at j (open_ty_rec j U T) -> lc_ty_at (S j) T.
Proof.
  intros j U T. revert j. induction T; intros j H; simpl in *.
  - destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_ty_bvar. lia.
    + apply lc_ty_bvar. inversion H. lia.
  - constructor.
  - inversion H; subst. constructor; auto.
  - inversion H; subst. constructor. apply IHT in H2. exact H2.
Qed.

Lemma lc_ty_open_fwd : forall j U T,
  lc_ty_at (S j) T -> lc_ty_at j U -> lc_ty_at j (open_ty_rec j U T).
Proof.
  intros j U T. revert j. induction T; intros j HT HU; simpl in *.
  - inversion HT; subst. destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact HU.
    + apply Nat.eqb_neq in E. constructor. lia.
  - constructor.
  - inversion HT; subst. constructor; auto.
  - inversion HT; subst. constructor. apply IHT; auto. apply lc_ty_at_mono with (k := j); auto; lia.
Qed.

Lemma lc_tm_open_ty_inv : forall j k U t,
  lc_tm_at j k (open_tm_ty_rec j U t) -> lc_tm_at (S j) k t.
Proof.
  intros j k U t. revert j k.
  induction t as [ n | a | T b IH | t1 IH1 t2 IH2 | b IH | a IH T | t1 IH1 t2 IH2 ];
  intros j k H; simpl in *.
  - inversion H. apply lc_tm_bvar. lia.
  - constructor.
  - apply lc_tm_abs_inv in H. destruct H as [Hty Hb]. constructor.
    + apply lc_ty_open_inv with (U := U). exact Hty.
    + apply IH. exact Hb.
  - apply lc_tm_app_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH1. exact H1.
    + apply IH2. exact H2.
  - apply lc_tm_tabs_inv in H. constructor. apply IH. exact H.
  - apply lc_tm_tapp_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH. exact H1.
    + apply lc_ty_open_inv with (U := U). exact H2.
  - apply lc_tm_choice_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH1. exact H1.
    + apply IH2. exact H2.
Qed.

Lemma lc_tm_open_ty_fwd : forall j k U t,
  lc_tm_at (S j) k t -> lc_ty_at j U -> lc_tm_at j k (open_tm_ty_rec j U t).
Proof.
  intros j k U t. revert j k.
  induction t as [ n | a | T b IH | t1 IH1 t2 IH2 | b IH | a IH T | t1 IH1 t2 IH2 ];
  intros j k H HU; simpl in *.
  - inversion H. apply lc_tm_bvar. lia.
  - constructor.
  - apply lc_tm_abs_inv in H. destruct H as [Hty Hb]. constructor.
    + apply lc_ty_open_fwd; auto.
    + apply IH; auto.
  - apply lc_tm_app_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH1; auto.
    + apply IH2; auto.
  - apply lc_tm_tabs_inv in H. constructor. apply IH; auto.
    apply lc_ty_at_mono with (k := j); auto; lia.
  - apply lc_tm_tapp_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH; auto.
    + apply lc_ty_open_fwd; auto.
  - apply lc_tm_choice_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH1; auto.
    + apply IH2; auto.
Qed.

Lemma lc_tm_open_tm_inv : forall K k u t,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K 0 u -> lc_tm_at K (S k) t.
Proof.
  intros K k u t. revert K k.
  induction t as [ n | a | T b IH | t1 IH1 t2 IH2 | b IH | a IH T | t1 IH1 t2 IH2 ];
  intros K k H Hu; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_bvar. lia.
    + inversion H. apply lc_tm_bvar. lia.
  - constructor.
  - apply lc_tm_abs_inv in H. destruct H as [Hty Hb]. constructor.
    + exact Hty.
    + apply IH; auto.
  - apply lc_tm_app_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH1; auto.
    + apply IH2; auto.
  - apply lc_tm_tabs_inv in H. constructor. apply IH; auto.
    apply lc_tm_at_mono with (K := K) (k := 0); auto; lia.
  - apply lc_tm_tapp_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH; auto.
    + exact H2.
  - apply lc_tm_choice_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH1; auto.
    + apply IH2; auto.
Qed.

Lemma lc_tm_open_tm_fwd : forall K k u t,
  lc_tm_at K (S k) t -> lc_tm_at K 0 u -> lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k u t. revert K k.
  induction t as [ n | a | T b IH | t1 IH1 t2 IH2 | b IH | a IH T | t1 IH1 t2 IH2 ];
  intros K k H Hu; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. apply lc_tm_at_mono with (K := K) (k := 0); auto; lia.
    + apply Nat.eqb_neq in E. inversion H. apply lc_tm_bvar. lia.
  - constructor.
  - apply lc_tm_abs_inv in H. destruct H as [Hty Hb]. constructor.
    + exact Hty.
    + apply IH; auto.
  - apply lc_tm_app_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH1; auto.
    + apply IH2; auto.
  - apply lc_tm_tabs_inv in H. constructor. apply IH; auto.
    apply lc_tm_at_mono with (K := K) (k := 0); auto; lia.
  - apply lc_tm_tapp_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH; auto.
    + exact H2.
  - apply lc_tm_choice_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH1; auto.
    + apply IH2; auto.
Qed.

Lemma lc_ty_tysub : forall sig, (forall X, lc_ty_at 0 (sig X)) ->
  forall k T, lc_ty_at k (tysub sig T) <-> lc_ty_at k T.
Proof.
  intros sig Hs k T. revert k. induction T; intros k; simpl.
  - tauto.
  - split; intros H.
    + constructor.
    + apply lc_ty_at_mono with (k := 0); auto; lia.
  - split; intros H.
    + apply lc_ty_arrow_inv in H. destruct H as [H1 H2].
      constructor; [apply (proj1 (IHT1 k)) | apply (proj1 (IHT2 k))]; auto.
    + apply lc_ty_arrow_inv in H. destruct H as [H1 H2].
      constructor; [apply (proj2 (IHT1 k)) | apply (proj2 (IHT2 k))]; auto.
  - split; intros H.
    + apply lc_ty_all_inv in H. constructor. apply (proj1 (IHT (S k))); auto.
    + apply lc_ty_all_inv in H. constructor. apply (proj2 (IHT (S k))); auto.
Qed.

Lemma lc_tm_tmsubst_ty : forall sig, (forall X, lc_ty_at 0 (sig X)) ->
  forall K k t, lc_tm_at K k (tmsubst_ty sig t) <-> lc_tm_at K k t.
Proof.
  intros sig Hs K k t. revert K k.
  induction t as [ n | a | T b IH | t1 IH1 t2 IH2 | b IH | a IH T | t1 IH1 t2 IH2 ];
  intros K k; simpl.
  - tauto.
  - tauto.
  - split; intros H.
    + apply lc_tm_abs_inv in H. destruct H as [Hty Hb]. constructor.
      * apply (proj1 (lc_ty_tysub sig Hs K T)); exact Hty.
      * apply IH. exact Hb.
    + apply lc_tm_abs_inv in H. destruct H as [Hty Hb]. constructor.
      * apply (proj2 (lc_ty_tysub sig Hs K T)); exact Hty.
      * apply IH. exact Hb.
  - split; intros H.
    + apply lc_tm_app_inv in H. destruct H as [H1 H2]. constructor.
      * apply IH1. exact H1.
      * apply IH2. exact H2.
    + apply lc_tm_app_inv in H. destruct H as [H1 H2]. constructor.
      * apply IH1. exact H1.
      * apply IH2. exact H2.
  - split; intros H.
    + apply lc_tm_tabs_inv in H. constructor. apply IH. exact H.
    + apply lc_tm_tabs_inv in H. constructor. apply IH. exact H.
  - split; intros H.
    + apply lc_tm_tapp_inv in H. destruct H as [H1 H2]. constructor.
      * apply IH. exact H1.
      * apply (proj1 (lc_ty_tysub sig Hs K T)); exact H2.
    + apply lc_tm_tapp_inv in H. destruct H as [H1 H2]. constructor.
      * apply IH. exact H1.
      * apply (proj2 (lc_ty_tysub sig Hs K T)); exact H2.
  - split; intros H.
    + apply lc_tm_choice_inv in H. destruct H as [H1 H2]. constructor.
      * apply IH1. exact H1.
      * apply IH2. exact H2.
    + apply lc_tm_choice_inv in H. destruct H as [H1 H2]. constructor.
      * apply IH1. exact H1.
      * apply IH2. exact H2.
Qed.

Lemma lc_tm_tmsubst_fv : forall gam, (forall x, lc_tm_at 0 0 (gam x)) ->
  forall K k t, lc_tm_at K k t -> lc_tm_at K k (tmsubst_fv gam t).
Proof.
  intros gam Hg K k t. revert K k.
  induction t as [ n | a | T b IH | t1 IH1 t2 IH2 | b IH | a IH T | t1 IH1 t2 IH2 ];
  intros K k H; simpl in *.
  - exact H.
  - apply lc_tm_at_mono with (K := 0) (k := 0); auto; lia.
  - apply lc_tm_abs_inv in H. destruct H as [Hty Hb]. constructor.
    + exact Hty.
    + apply IH. exact Hb.
  - apply lc_tm_app_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH1. exact H1.
    + apply IH2. exact H2.
  - apply lc_tm_tabs_inv in H. constructor. apply IH. exact H.
  - apply lc_tm_tapp_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH. exact H1.
    + exact H2.
  - apply lc_tm_choice_inv in H. destruct H as [H1 H2]. constructor.
    + apply IH1. exact H1.
    + apply IH2. exact H2.
Qed.

(* ----------------------------------------------------------------- *)
(* Well-formed types and typing judgments are locally closed          *)
(* ----------------------------------------------------------------- *)

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H.
  induction H as [ Delta X Hin
                 | Delta T1 T2 H1 IH1 H2 IH2
                 | L Delta T Hprem IH ].
  - constructor.
  - constructor; auto.
  - constructor.
    assert (HX : ~ In (fresh_atom L) L) by apply fresh_atom_notin.
    specialize (IH (fresh_atom L) HX).
    apply (lc_ty_open_inv 0 (Ty_FVar (fresh_atom L)) T) in IH.
    exact IH.
Qed.

Lemma lookup_context_In : forall x Gamma T,
  lookup_context x Gamma = Some T -> In (x, T) Gamma.
Proof.
  intros x Gamma. induction Gamma as [| [y S] G IH]; intros T H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + apply Nat.eqb_eq in E. subst. inversion H; subst. simpl. auto.
    + simpl. right. apply IH; auto.
Qed.

Lemma In_ctx_vars : forall Gamma x T, In (x, T) Gamma -> In x (ctx_vars Gamma).
Proof.
  intros Gamma. induction Gamma as [| [y S] G IH]; intros x T H; simpl in *.
  - inversion H.
  - destruct H as [Heq | H].
    + inversion Heq; subst. simpl. auto.
    + simpl. right. apply (IH x T); auto.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at 0 0 t /\ lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H.
  induction H as [ Delta Gamma x T Hlk Hwf
                 | L Delta Gamma T1 t2 T2 Hwf Hprem Hbody
                 | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta Gamma t T Hprem Hbody
                 | Delta Gamma t T U H1 IH1 Hwf
                 | Delta Gamma t1 t2 T H1 IH1 H2 IH2 ].
  - (* T_Var *) split.
    + apply lc_tm_fvar.
    + apply wf_ty_lc with (Delta := Delta); auto.
  - (* T_Abs *) split.
    + apply lc_tm_abs.
      * apply wf_ty_lc with (Delta := Delta); auto.
      * assert (Hx : ~ In (fresh_atom L) L) by apply fresh_atom_notin.
        destruct (Hbody (fresh_atom L) Hx) as [Hlc _].
        eapply lc_tm_open_tm_inv; [exact Hlc | apply lc_tm_fvar].
    + apply lc_ty_arrow.
      * apply wf_ty_lc with (Delta := Delta); auto.
      * assert (Hx : ~ In (fresh_atom L) L) by apply fresh_atom_notin.
        destruct (Hbody (fresh_atom L) Hx) as [_ HT]. exact HT.
  - (* T_App *) split.
    + apply lc_tm_app; [apply IH1 | apply IH2].
    + destruct IH1 as [_ HT]. apply lc_ty_arrow_inv in HT. destruct HT as [_ Hres]. exact Hres.
  - (* T_TAbs *) split.
    + assert (HX : ~ In (fresh_atom L) L) by apply fresh_atom_notin.
      destruct (Hbody (fresh_atom L) HX) as [Hlc _].
      apply (lc_tm_open_ty_inv 0 0 (Ty_FVar (fresh_atom L)) t) in Hlc.
      simpl in Hlc. apply lc_tm_tabs. exact Hlc.
    + assert (HX : ~ In (fresh_atom L) L) by apply fresh_atom_notin.
      destruct (Hbody (fresh_atom L) HX) as [_ HT].
      apply (lc_ty_open_inv 0 (Ty_FVar (fresh_atom L)) T) in HT.
      simpl in HT. apply lc_ty_all. exact HT.
  - (* T_TApp *) split.
    + apply lc_tm_tapp; [apply IH1 | apply wf_ty_lc with (Delta := Delta); auto].
    + destruct IH1 as [_ HT]. apply lc_ty_all_inv in HT.
      apply lc_ty_open_fwd; auto. apply wf_ty_lc with (Delta := Delta); auto.
  - (* T_Choice *) split.
    + apply lc_tm_choice; [apply IH1 | apply IH2].
    + destruct IH1 as [_ HT]. exact HT.
Qed.

Lemma has_type_fv : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall x, In x (fv_tm t) -> In x (ctx_vars Gamma).
Proof.
  intros Delta Gamma t T H.
  induction H as [ Delta Gamma x T Hlk Hwf
                 | L Delta Gamma T1 t2 T2 Hwf Hprem Hbody
                 | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta Gamma t T Hprem Hbody
                 | Delta Gamma t T U H1 IH1 Hwf
                 | Delta Gamma t1 t2 T H1 IH1 H2 IH2 ];
  intros y Hy.
  - (* T_Var *) simpl in Hy. destruct Hy as [-> | []].
    apply In_ctx_vars with (T := T). apply lookup_context_In. exact Hlk.
  - (* T_Abs *) simpl in Hy.
    set (x := fresh_atom (L ++ fv_tm t2 ++ ctx_vars Gamma)).
    assert (Hxall : ~ In x (L ++ fv_tm t2 ++ ctx_vars Gamma)).
    { subst x. apply fresh_atom_notin. }
    assert (Hx : ~ In x L).
    { intros Hin. apply Hxall. apply in_app_iff. left. exact Hin. }
    assert (Hxfv : ~ In x (fv_tm t2)).
    { intros Hin. apply Hxall. apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
    assert (Hy' : In y (fv_tm (open_tm_rec 0 (tm_fvar x) t2))).
    { apply In_fv_tm_open_fwd. exact Hy. }
    specialize (Hbody x Hx). apply Hbody in Hy'. simpl in Hy'.
    destruct Hy' as [Heq | Hy'].
    + exfalso. rewrite <- Heq in Hy. exact (Hxfv Hy).
    + exact Hy'.
  - (* T_App *) simpl in Hy. apply in_app_iff in Hy. destruct Hy as [Hy | Hy].
    + apply IH1; exact Hy.
    + apply IH2; exact Hy.
  - (* T_TAbs *) simpl in Hy.
    assert (HX : ~ In (fresh_atom L) L) by apply fresh_atom_notin.
    specialize (Hbody (fresh_atom L) HX).
    apply Hbody. apply In_fv_tm_ty_open. exact Hy.
  - (* T_TApp *) simpl in Hy. apply IH1; exact Hy.
  - (* T_Choice *) simpl in Hy. apply in_app_iff in Hy. destruct Hy as [Hy | Hy].
    + apply IH1; exact Hy.
    + apply IH2; exact Hy.
Qed.

(* ================================================================= *)
(* The logical relation                                              *)
(* ================================================================= *)

Definition rel := tm -> tm -> Prop.
Definition tenv := atom -> rel.
Definition rstack := list rel.

Fixpoint nth_rel (rs : rstack) (i : nat) : rel :=
  match rs, i with
  | [], _ => fun _ _ => False
  | R :: _, 0 => R
  | _ :: rs', S i' => nth_rel rs' i'
  end.

Lemma nth_rel_cons_0 : forall (R : rel) rs, nth_rel (R :: rs) 0 = R.
Proof. reflexivity. Qed.

Lemma nth_rel_cons_S : forall (R : rel) rs i, nth_rel (R :: rs) (S i) = nth_rel rs i.
Proof. reflexivity. Qed.

Lemma nth_rel_insert_same : forall k (rs : rstack) (R : rel),
  k <= length rs -> nth_rel (firstn k rs ++ R :: skipn k rs) k = R.
Proof.
  induction k as [|k IH]; intros rs R Hlen.
  - simpl. reflexivity.
  - destruct rs as [|R0 rs]; [simpl in Hlen; lia|].
    simpl. apply IH. simpl in Hlen. lia.
Qed.

Lemma nth_rel_insert_below : forall k (rs : rstack) (R : rel) i,
  i < k -> i < length rs ->
  nth_rel (firstn k rs ++ R :: skipn k rs) i = nth_rel rs i.
Proof.
  induction k as [|k IH]; intros rs R i Hi Hlen.
  - lia.
  - destruct rs as [|R0 rs]; [simpl in Hlen; lia|].
    destruct i as [|i].
    + simpl. reflexivity.
    + simpl in Hi, Hlen. simpl. apply IH; lia.
Qed.

Definition extend (rho : tenv) (X : atom) (R : rel) : tenv :=
  fun Y => if Nat.eqb Y X then R else rho Y.

Lemma extend_same : forall rho X R, extend rho X R X = R.
Proof. intros. unfold extend. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma extend_other : forall rho X R Y, Y <> X -> extend rho X R Y = rho Y.
Proof. intros. unfold extend. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

(* Vb is the body of the relation at a type; V adds the value requirement
   at the top.  Vb T rs rho w1 w2 where rs is the stack of relations
   interpreting the free de Bruijn type variables (innermost first). *)

Fixpoint Vb (T : ty) (rs : rstack) (rho : tenv) (w1 w2 : tm) {struct T} : Prop :=
  match T with
  | Ty_FVar X => rho X w1 w2
  | Ty_BVar i => nth_rel rs i w1 w2
  | Ty_Arrow T1 T2 =>
      exists Ta b1 Tb b2,
        w1 = tm_abs Ta b1 /\ w2 = tm_abs Tb b2 /\
        (forall a1 a2,
            value a1 /\ value a2 /\ Vb T1 rs rho a1 a2 ->
            exists z1 z2, value z1 /\ value z2 /\
              open_tm b1 a1 -->* z1 /\ open_tm b2 a2 -->* z2 /\
              Vb T2 rs rho z1 z2)
  | Ty_All T1 =>
      exists b1 b2,
        w1 = tm_tabs b1 /\ w2 = tm_tabs b2 /\
        (forall (U1 U2 : ty) (R : rel),
            lc_ty_at 0 U1 -> lc_ty_at 0 U2 ->
            exists z1 z2, value z1 /\ value z2 /\
              open_tm_ty b1 U1 -->* z1 /\ open_tm_ty b2 U2 -->* z2 /\
              Vb T1 (R :: rs) rho z1 z2)
  end.

Definition V (T : ty) (rs : rstack) (rho : tenv) (w1 w2 : tm) : Prop :=
  value w1 /\ value w2 /\ Vb T rs rho w1 w2.

Definition E (T : ty) (rs : rstack) (rho : tenv) (e1 e2 : tm) : Prop :=
  exists w1 w2, value w1 /\ value w2 /\ e1 -->* w1 /\ e2 -->* w2 /\ Vb T rs rho w1 w2.

Lemma Vb_arrow : forall T1 T2 rs rho w1 w2,
  Vb (Ty_Arrow T1 T2) rs rho w1 w2 <->
  (exists Ta b1 Tb b2,
      w1 = tm_abs Ta b1 /\ w2 = tm_abs Tb b2 /\
      (forall a1 a2, V T1 rs rho a1 a2 -> E T2 rs rho (open_tm b1 a1) (open_tm b2 a2))).
Proof. intros. simpl. reflexivity. Qed.

Lemma Vb_all : forall T1 rs rho w1 w2,
  Vb (Ty_All T1) rs rho w1 w2 <->
  (exists b1 b2,
      w1 = tm_tabs b1 /\ w2 = tm_tabs b2 /\
      (forall (U1 U2 : ty) (R : rel), lc_ty_at 0 U1 -> lc_ty_at 0 U2 ->
          E T1 (R :: rs) rho (open_tm_ty b1 U1) (open_tm_ty b2 U2))).
Proof. intros. simpl. reflexivity. Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof. intros v H. inversion H; subst; auto. Qed.

(* Multi-step helper lemmas *)

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c H1 H2. induction H1.
  - exact H2.
  - eapply multi_step; eauto.
Qed.

Lemma multi_app_l : forall a a' b,
  a -->* a' -> locally_closed_tm b -> tm_app a b -->* tm_app a' b.
Proof.
  intros a a' b H Hlc. induction H as [x | x y z Hstep Htail IH].
  - apply multi_refl.
  - eapply multi_step.
    + eapply ST_App1; eauto.
    + exact IH.
Qed.

Lemma multi_app_r : forall a b b',
  value a -> b -->* b' -> tm_app a b -->* tm_app a b'.
Proof.
  intros a b b' Hv H. induction H as [x | x y z Hstep Htail IH].
  - apply multi_refl.
  - eapply multi_step.
    + eapply ST_App2; eauto.
    + exact IH.
Qed.

Lemma multi_tapp : forall a a' T,
  a -->* a' -> locally_closed_ty T -> tm_tapp a T -->* tm_tapp a' T.
Proof.
  intros a a' T H Hlc. induction H as [x | x y z Hstep Htail IH].
  - apply multi_refl.
  - eapply multi_step.
    + eapply ST_TApp; eauto.
    + exact IH.
Qed.

Lemma value_no_step : forall v u, value v -> ~ (v --> u).
Proof.
  intros v u Hv Hs. inversion Hv; subst; inversion Hs.
Qed.

Lemma multi_value : forall v u, value v -> v -->* u -> u = v.
Proof.
  intros v u Hv Hm. induction Hm.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

Lemma E_mono_multi : forall T rs rho e1 e1' e2 e2',
  e1 -->* e1' -> e2 -->* e2' -> E T rs rho e1' e2' -> E T rs rho e1 e2.
Proof.
  intros T rs rho e1 e1' e2 e2' H1 H2 (w1 & w2 & Hv1 & Hv2 & Hm1 & Hm2 & HV).
  exists w1, w2.
  split; [exact Hv1 | split; [exact Hv2 | split;
    [eapply multi_trans; eauto | split; [eapply multi_trans; eauto | exact HV]]]].
Qed.

(* ----------------------------------------------------------------- *)
(* Environment congruence for the relation (free type atoms)          *)
(* ----------------------------------------------------------------- *)

Lemma Vb_arrow_transfer : forall T1a T2a T1b T2b rs1 rs2 rho1 rho2,
  (forall a1 a2, V T1a rs1 rho1 a1 a2 <-> V T1b rs2 rho2 a1 a2) ->
  (forall z1 z2, Vb T2a rs1 rho1 z1 z2 <-> Vb T2b rs2 rho2 z1 z2) ->
  forall w1 w2, Vb (Ty_Arrow T1a T2a) rs1 rho1 w1 w2 <-> Vb (Ty_Arrow T1b T2b) rs2 rho2 w1 w2.
Proof.
  intros T1a T2a T1b T2b rs1 rs2 rho1 rho2 H1 H2 w1 w2. simpl.
  assert (F : Vb (Ty_Arrow T1a T2a) rs1 rho1 w1 w2 ->
              Vb (Ty_Arrow T1b T2b) rs2 rho2 w1 w2).
  { intros (Ta & b1 & Tb & b2 & Heq1 & Heq2 & Hcl).
    exists Ta, b1, Tb, b2. split; [exact Heq1 | split; [exact Heq2 |]].
    intros a1 a2 Ha.
    destruct Ha as (Hva1 & Hva2 & HVb2).
    assert (HVb1 : Vb T1a rs1 rho1 a1 a2).
    { apply (proj2 (H1 a1 a2)).
      split; [exact Hva1 | split; [exact Hva2 | exact HVb2]]. }
    assert (Ha1 : value a1 /\ value a2 /\ Vb T1a rs1 rho1 a1 a2).
    { split; [exact Hva1 | split; [exact Hva2 | exact HVb1]]. }
    destruct (Hcl a1 a2 Ha1) as (z1 & z2 & Hz1 & Hz2 & Hm1 & Hm2 & HV).
    exists z1, z2.
    split; [exact Hz1 | split; [exact Hz2 | split; [exact Hm1 | split;
      [exact Hm2 | apply (proj1 (H2 z1 z2)); exact HV]]]]. }
  assert (B : Vb (Ty_Arrow T1b T2b) rs2 rho2 w1 w2 ->
              Vb (Ty_Arrow T1a T2a) rs1 rho1 w1 w2).
  { intros (Ta & b1 & Tb & b2 & Heq1 & Heq2 & Hcl).
    exists Ta, b1, Tb, b2. split; [exact Heq1 | split; [exact Heq2 |]].
    intros a1 a2 Ha.
    destruct Ha as (Hva1 & Hva2 & HVb1).
    assert (HVb2 : Vb T1b rs2 rho2 a1 a2).
    { apply (proj1 (H1 a1 a2)).
      split; [exact Hva1 | split; [exact Hva2 | exact HVb1]]. }
    assert (Ha2 : value a1 /\ value a2 /\ Vb T1b rs2 rho2 a1 a2).
    { split; [exact Hva1 | split; [exact Hva2 | exact HVb2]]. }
    destruct (Hcl a1 a2 Ha2) as (z1 & z2 & Hz1 & Hz2 & Hm1 & Hm2 & HV).
    exists z1, z2.
    split; [exact Hz1 | split; [exact Hz2 | split; [exact Hm1 | split;
      [exact Hm2 | apply (proj2 (H2 z1 z2)); exact HV]]]]. }
  split; assumption.
Qed.

Lemma Vb_all_transfer : forall T1a T1b rs1 rs2 rho1 rho2,
  (forall R z1 z2, Vb T1a (R :: rs1) rho1 z1 z2 <-> Vb T1b (R :: rs2) rho2 z1 z2) ->
  forall w1 w2, Vb (Ty_All T1a) rs1 rho1 w1 w2 <-> Vb (Ty_All T1b) rs2 rho2 w1 w2.
Proof.
  intros T1a T1b rs1 rs2 rho1 rho2 H w1 w2. simpl.
  assert (F : Vb (Ty_All T1a) rs1 rho1 w1 w2 -> Vb (Ty_All T1b) rs2 rho2 w1 w2).
  { intros (b1 & b2 & Heq1 & Heq2 & Hcl).
    exists b1, b2. split; [exact Heq1 | split; [exact Heq2 |]].
    intros U1 U2 R HU1 HU2.
    destruct (Hcl U1 U2 R HU1 HU2) as (z1 & z2 & Hz1 & Hz2 & Hm1 & Hm2 & HV).
    exists z1, z2.
    split; [exact Hz1 | split; [exact Hz2 | split; [exact Hm1 | split;
      [exact Hm2 | apply (proj1 (H R z1 z2)); exact HV]]]]. }
  assert (B : Vb (Ty_All T1b) rs2 rho2 w1 w2 -> Vb (Ty_All T1a) rs1 rho1 w1 w2).
  { intros (b1 & b2 & Heq1 & Heq2 & Hcl).
    exists b1, b2. split; [exact Heq1 | split; [exact Heq2 |]].
    intros U1 U2 R HU1 HU2.
    destruct (Hcl U1 U2 R HU1 HU2) as (z1 & z2 & Hz1 & Hz2 & Hm1 & Hm2 & HV).
    exists z1, z2.
    split; [exact Hz1 | split; [exact Hz2 | split; [exact Hm1 | split;
      [exact Hm2 | apply (proj2 (H R z1 z2)); exact HV]]]]. }
  split; assumption.
Qed.

Lemma Vb_env_cong : forall T,
  (forall rs rho1 rho2,
    (forall X, In X (atoms_ty T) -> forall w1 w2, rho1 X w1 w2 <-> rho2 X w1 w2) ->
    forall w1 w2, Vb T rs rho1 w1 w2 <-> Vb T rs rho2 w1 w2).
Proof.
  intros T. induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1].
  - (* BVar *) intros rs rho1 rho2 Hag w1 w2. simpl. tauto.
  - (* FVar *) intros rs rho1 rho2 Hag w1 w2. simpl.
    destruct (Hag X (or_introl eq_refl) w1 w2) as [Hf Hb]. split; auto.
  - (* Arrow *) intros rs rho1 rho2 Hag w1 w2.
    assert (Hag1 : forall Y, In Y (atoms_ty T1) -> forall a1 a2, rho1 Y a1 a2 <-> rho2 Y a1 a2).
    { intros Y HY a1 a2. apply Hag. apply in_app_iff. left. exact HY. }
    assert (Hag2 : forall Y, In Y (atoms_ty T2) -> forall a1 a2, rho1 Y a1 a2 <-> rho2 Y a1 a2).
    { intros Y HY a1 a2. apply Hag. apply in_app_iff. right. exact HY. }
    apply Vb_arrow_transfer.
    + intros a1 a2. unfold V.
      destruct (IH1 rs rho1 rho2 Hag1 a1 a2) as [Hf Hb]. split.
      * intros (X1 & X2 & X3). split; [exact X1 | split; [exact X2 | apply Hf; exact X3]].
      * intros (X1 & X2 & X3). split; [exact X1 | split; [exact X2 | apply Hb; exact X3]].
    + apply IH2. exact Hag2.
  - (* All *) intros rs rho1 rho2 Hag w1 w2.
    apply Vb_all_transfer. intros R z1 z2.
    apply IH1. exact Hag.
Qed.

Lemma V_env_cong : forall T rs rho1 rho2,
  (forall X, In X (atoms_ty T) -> forall w1 w2, rho1 X w1 w2 <-> rho2 X w1 w2) ->
  forall w1 w2, V T rs rho1 w1 w2 <-> V T rs rho2 w1 w2.
Proof.
  intros T rs rho1 rho2 Hag w1 w2. unfold V.
  destruct (Vb_env_cong T rs rho1 rho2 Hag w1 w2) as [Hf Hb]. split.
  - intros (H1 & H2 & H3). split; [exact H1 | split; [exact H2 | apply Hf; exact H3]].
  - intros (H1 & H2 & H3). split; [exact H1 | split; [exact H2 | apply Hb; exact H3]].
Qed.

Lemma E_env_cong : forall T rs rho1 rho2,
  (forall X, In X (atoms_ty T) -> forall w1 w2, rho1 X w1 w2 <-> rho2 X w1 w2) ->
  forall e1 e2, E T rs rho1 e1 e2 <-> E T rs rho2 e1 e2.
Proof.
  intros T rs rho1 rho2 Hag e1 e2. unfold E.
  split.
  - intros (w1 & w2 & H1 & H2 & Hm1 & Hm2 & HV).
    destruct (Vb_env_cong T rs rho1 rho2 Hag w1 w2) as [Hf Hb].
    exists w1, w2. split; [exact H1 | split; [exact H2 | split;
      [exact Hm1 | split; [exact Hm2 | apply Hf; exact HV]]]].
  - intros (w1 & w2 & H1 & H2 & Hm1 & Hm2 & HV).
    destruct (Vb_env_cong T rs rho1 rho2 Hag w1 w2) as [Hf Hb].
    exists w1, w2. split; [exact H1 | split; [exact H2 | split;
      [exact Hm1 | split; [exact Hm2 | apply Hb; exact HV]]]].
Qed.

(* ----------------------------------------------------------------- *)
(* Stack congruence for the relation (de Bruijn type variables)       *)
(* ----------------------------------------------------------------- *)

Definition rels_agree_below (k : nat) (rs1 rs2 : rstack) : Prop :=
  (forall i, i < k -> forall w1 w2, nth_rel rs1 i w1 w2 <-> nth_rel rs2 i w1 w2) /\
  length rs1 >= k /\ length rs2 >= k.

Lemma rels_agree_below_0 : forall rs1 rs2, rels_agree_below 0 rs1 rs2.
Proof.
  intros. unfold rels_agree_below. split; [| split; lia].
  intros i Hi. lia.
Qed.

Lemma rels_agree_below_S : forall k rs1 rs2 R,
  rels_agree_below k rs1 rs2 -> rels_agree_below (S k) (R :: rs1) (R :: rs2).
Proof.
  intros k rs1 rs2 R (Hp & Hl1 & Hl2). split; [| split; simpl; lia].
  intros i Hi. destruct i as [|i].
  - simpl. reflexivity.
  - simpl. apply Hp. lia.
Qed.

Lemma nth_error_some_of_lt : forall (l : rstack) i, i < length l -> exists R, nth_error l i = Some R.
Proof.
  intros l. induction l as [|R l IH]; intros i Hi; simpl in *.
  - lia.
  - destruct i as [|i].
    + exists R. reflexivity.
    + simpl. apply IH. lia.
Qed.

Lemma nth_error_insert_same : forall k (rs : rstack) (R : rel),
  k <= length rs -> @nth_error rel (firstn k rs ++ R :: skipn k rs) k = Some R.
Proof.
  intros k. induction k as [|k IH]; intros rs R Hlen.
  - simpl. reflexivity.
  - destruct rs as [|R0 rs]. { simpl in Hlen. lia. }
    simpl. apply IH. simpl in Hlen. lia.
Qed.

Lemma nth_error_insert_below : forall k (rs : rstack) (R : rel) i,
  i < k -> i < length rs ->
  @nth_error rel (firstn k rs ++ R :: skipn k rs) i = @nth_error rel rs i.
Proof.
  intros k. induction k as [|k IH]; intros rs R i Hi Hlen.
  - lia.
  - destruct rs as [|R0 rs].
    + simpl in Hlen. lia.
    + destruct i as [|i].
      * simpl. reflexivity.
      * simpl in Hi, Hlen. simpl. apply IH; lia.
Qed.

Lemma Vb_stack_agree : forall T,
  (forall k, lc_ty_at k T ->
    forall rs1 rs2 rho, rels_agree_below k rs1 rs2 ->
    forall w1 w2, Vb T rs1 rho w1 w2 <-> Vb T rs2 rho w1 w2).
Proof.
  intros T. induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1].
  - (* BVar *) intros k Hlc rs1 rs2 rho Hag w1 w2. simpl.
    apply lc_ty_bvar_inv in Hlc.
    destruct Hag as (Hp & Hl1 & Hl2).
    apply Hp; auto.
  - (* FVar *) intros k Hlc rs1 rs2 rho Hag w1 w2. simpl. tauto.
  - (* Arrow *) intros k Hlc rs1 rs2 rho Hag w1 w2.
    apply lc_ty_arrow_inv in Hlc. destruct Hlc as (Hlc1 & Hlc2).
    apply Vb_arrow_transfer.
    + intros a1 a2. unfold V.
      destruct (IH1 k Hlc1 rs1 rs2 rho Hag a1 a2) as [Hf Hb]. split.
      * intros (X1 & X2 & X3). split; [exact X1 | split; [exact X2 | apply Hf; exact X3]].
      * intros (X1 & X2 & X3). split; [exact X1 | split; [exact X2 | apply Hb; exact X3]].
    + exact (IH2 k Hlc2 rs1 rs2 rho Hag).
  - (* All *) intros k Hlc rs1 rs2 rho Hag w1 w2.
    apply lc_ty_all_inv in Hlc.
    apply Vb_all_transfer. intros R z1 z2.
    exact (IH1 (S k) Hlc (R :: rs1) (R :: rs2) rho (rels_agree_below_S k rs1 rs2 R Hag) z1 z2).
Qed.

Lemma V_stack_agree : forall T k,
  lc_ty_at k T ->
  forall rs1 rs2 rho, rels_agree_below k rs1 rs2 ->
  forall w1 w2, V T rs1 rho w1 w2 <-> V T rs2 rho w1 w2.
Proof.
  intros T k Hlc rs1 rs2 rho Hag w1 w2. unfold V.
  destruct (Vb_stack_agree T k Hlc rs1 rs2 rho Hag w1 w2) as [Hf Hb]. split.
  - intros (H1 & H2 & H3). split; [exact H1 | split; [exact H2 | apply Hf; exact H3]].
  - intros (H1 & H2 & H3). split; [exact H1 | split; [exact H2 | apply Hb; exact H3]].
Qed.

Lemma E_stack_agree : forall T k,
  lc_ty_at k T ->
  forall rs1 rs2 rho, rels_agree_below k rs1 rs2 ->
  forall e1 e2, E T rs1 rho e1 e2 <-> E T rs2 rho e1 e2.
Proof.
  intros T k Hlc rs1 rs2 rho Hag e1 e2. unfold E.
  split.
  - intros (w1 & w2 & H1 & H2 & Hm1 & Hm2 & HV).
    destruct (Vb_stack_agree T k Hlc rs1 rs2 rho Hag w1 w2) as [Hf Hb].
    exists w1, w2. split; [exact H1 | split; [exact H2 | split;
      [exact Hm1 | split; [exact Hm2 | apply Hf; exact HV]]]].
  - intros (w1 & w2 & H1 & H2 & Hm1 & Hm2 & HV).
    destruct (Vb_stack_agree T k Hlc rs1 rs2 rho Hag w1 w2) as [Hf Hb].
    exists w1, w2. split; [exact H1 | split; [exact H2 | split;
      [exact Hm1 | split; [exact Hm2 | apply Hb; exact HV]]]].
Qed.

Lemma Vb_stack_any : forall T rs1 rs2 rho,
  lc_ty_at 0 T -> forall w1 w2, Vb T rs1 rho w1 w2 <-> Vb T rs2 rho w1 w2.
Proof.
  intros T rs1 rs2 rho Hlc w1 w2.
  apply Vb_stack_agree with (k := 0); auto.
  apply rels_agree_below_0.
Qed.

Lemma V_stack_any : forall T rs1 rs2 rho,
  lc_ty_at 0 T -> forall w1 w2, V T rs1 rho w1 w2 <-> V T rs2 rho w1 w2.
Proof.
  intros T rs1 rs2 rho Hlc w1 w2. apply V_stack_agree with (k := 0); auto.
  apply rels_agree_below_0.
Qed.

(* ----------------------------------------------------------------- *)
(* Opening lemmas: atom opening / type substitution versus stacks     *)
(* ----------------------------------------------------------------- *)

Lemma Vb_open_atom : forall T,
  (forall k X R rho rs,
    length rs = k -> lc_ty_at (S k) T -> ~ In X (atoms_ty T) ->
    forall w1 w2,
      Vb (open_ty_rec k (Ty_FVar X) T) rs (extend rho X R) w1 w2 <->
      Vb T (firstn k rs ++ R :: skipn k rs) rho w1 w2).
Proof.
  intros T. induction T as [i | Y | T1 IH1 T2 IH2 | T1 IH1].
  - (* BVar *) intros k X R rho rs Hlen Hlc Hf w1 w2. simpl.
    apply lc_ty_bvar_inv in Hlc.
    destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. simpl.
      assert (Hn : nth_rel (firstn k rs ++ R :: skipn k rs) k = R).
      { apply nth_rel_insert_same. lia. }
      rewrite Hn, extend_same. tauto.
    + apply Nat.eqb_neq in E.
      assert (Hi : i < k) by lia.
      assert (Hleni : i < length rs) by lia.
      simpl.
      assert (Hn : nth_rel (firstn k rs ++ R :: skipn k rs) i = nth_rel rs i).
      { apply nth_rel_insert_below; auto. }
      rewrite Hn. tauto.
  - (* FVar *) intros k X R rho rs Hlen Hlc Hf w1 w2. simpl.
    assert (Hne : Y <> X) by (intros ->; apply Hf; simpl; auto).
    rewrite extend_other by auto. tauto.
  - (* Arrow *) intros k X R rho rs Hlen Hlc Hf w1 w2.
    apply lc_ty_arrow_inv in Hlc. destruct Hlc as (Hlc1 & Hlc2).
    assert (Hf1 : ~ In X (atoms_ty T1)).
    { intros Hin. apply Hf. simpl. apply in_app_iff. left. exact Hin. }
    assert (Hf2 : ~ In X (atoms_ty T2)).
    { intros Hin. apply Hf. simpl. apply in_app_iff. right. exact Hin. }
    apply Vb_arrow_transfer.
    + intros a1 a2. unfold V.
      destruct (IH1 k X R rho rs Hlen Hlc1 Hf1 a1 a2) as [Hfst Hsnd]. split.
      * intros (A1 & A2 & A3). split; [exact A1 | split; [exact A2 | apply Hfst; exact A3]].
      * intros (A1 & A2 & A3). split; [exact A1 | split; [exact A2 | apply Hsnd; exact A3]].
    + intros z1 z2. apply IH2; auto.
  - (* All *) intros k X R rho rs Hlen Hlc Hf w1 w2.
    apply lc_ty_all_inv in Hlc.
    apply Vb_all_transfer. intros R' z1 z2.
    exact (IH1 (S k) X R rho (R' :: rs) (f_equal S Hlen) Hlc Hf z1 z2).
Qed.

Lemma Vb_open_subst : forall T,
  (forall k U rho rs,
    length rs = k -> lc_ty_at (S k) T -> lc_ty_at 0 U ->
    forall w1 w2,
      Vb (open_ty_rec k U T) rs rho w1 w2 <->
      Vb T (firstn k rs ++ Vb U [] rho :: skipn k rs) rho w1 w2).
Proof.
  intros T. induction T as [i | Y | T1 IH1 T2 IH2 | T1 IH1].
  - (* BVar *) intros k U rho rs Hlen Hlc HUn w1 w2. simpl.
    apply lc_ty_bvar_inv in Hlc.
    destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. subst i. simpl.
      assert (Hn : nth_rel (firstn k rs ++ Vb U [] rho :: skipn k rs) k = Vb U [] rho).
      { apply nth_rel_insert_same. lia. }
      rewrite Hn. apply Vb_stack_any; auto.
    + apply Nat.eqb_neq in E.
      assert (Hi : i < k) by lia.
      assert (Hleni : i < length rs) by lia.
      simpl.
      assert (Hn : nth_rel (firstn k rs ++ Vb U [] rho :: skipn k rs) i = nth_rel rs i).
      { apply nth_rel_insert_below; auto. }
      rewrite Hn. tauto.
  - (* FVar *) intros k U rho rs Hlen Hlc HUn w1 w2. simpl. tauto.
  - (* Arrow *) intros k U rho rs Hlen Hlc HUn w1 w2.
    apply lc_ty_arrow_inv in Hlc. destruct Hlc as (Hlc1 & Hlc2).
    apply Vb_arrow_transfer.
    + intros a1 a2. unfold V.
      destruct (IH1 k U rho rs Hlen Hlc1 HUn a1 a2) as [Hfst Hsnd]. split.
      * intros (A1 & A2 & A3). split; [exact A1 | split; [exact A2 | apply Hfst; exact A3]].
      * intros (A1 & A2 & A3). split; [exact A1 | split; [exact A2 | apply Hsnd; exact A3]].
    + intros z1 z2. apply IH2; auto.
  - (* All *) intros k U rho rs Hlen Hlc HUn w1 w2.
    apply lc_ty_all_inv in Hlc.
    apply Vb_all_transfer. intros R' z1 z2.
    exact (IH1 (S k) U rho (R' :: rs) (f_equal S Hlen) Hlc HUn z1 z2).
Qed.

Lemma V_open_atom : forall T rs k X R rho,
  length rs = k -> lc_ty_at (S k) T -> ~ In X (atoms_ty T) ->
  forall w1 w2,
    V (open_ty_rec k (Ty_FVar X) T) rs (extend rho X R) w1 w2 <->
    V T (firstn k rs ++ R :: skipn k rs) rho w1 w2.
Proof.
  intros T rs k X R rho Hlen Hlc Hf w1 w2. unfold V.
  destruct (Vb_open_atom T k X R rho rs Hlen Hlc Hf w1 w2) as [Hfw Hbw]. split.
  - intros (A1 & A2 & A3). split; [exact A1 | split; [exact A2 | apply Hfw; exact A3]].
  - intros (A1 & A2 & A3). split; [exact A1 | split; [exact A2 | apply Hbw; exact A3]].
Qed.

Lemma V_open_subst : forall T rs k U rho,
  length rs = k -> lc_ty_at (S k) T -> lc_ty_at 0 U ->
  forall w1 w2,
    V (open_ty_rec k U T) rs rho w1 w2 <->
    V T (firstn k rs ++ Vb U [] rho :: skipn k rs) rho w1 w2.
Proof.
  intros T rs k U rho Hlen Hlc HUn w1 w2. unfold V.
  destruct (Vb_open_subst T k U rho rs Hlen Hlc HUn w1 w2) as [Hfw Hbw]. split.
  - intros (A1 & A2 & A3). split; [exact A1 | split; [exact A2 | apply Hfw; exact A3]].
  - intros (A1 & A2 & A3). split; [exact A1 | split; [exact A2 | apply Hbw; exact A3]].
Qed.

Lemma E_open_atom : forall T rs k X R rho,
  length rs = k -> lc_ty_at (S k) T -> ~ In X (atoms_ty T) ->
  forall e1 e2,
    E (open_ty_rec k (Ty_FVar X) T) rs (extend rho X R) e1 e2 <->
    E T (firstn k rs ++ R :: skipn k rs) rho e1 e2.
Proof.
  intros T rs k X R rho Hlen Hlc Hf e1 e2. unfold E. split.
  - intros (w1 & w2 & A1 & A2 & Hm1 & Hm2 & HV).
    exists w1, w2. split; [exact A1 | split; [exact A2 | split;
      [exact Hm1 | split; [exact Hm2 |]]]].
    apply (proj1 (Vb_open_atom T k X R rho rs Hlen Hlc Hf w1 w2)); exact HV.
  - intros (w1 & w2 & A1 & A2 & Hm1 & Hm2 & HV).
    exists w1, w2. split; [exact A1 | split; [exact A2 | split;
      [exact Hm1 | split; [exact Hm2 |]]]].
    apply (proj2 (Vb_open_atom T k X R rho rs Hlen Hlc Hf w1 w2)); exact HV.
Qed.

Lemma E_open_subst : forall T rs k U rho,
  length rs = k -> lc_ty_at (S k) T -> lc_ty_at 0 U ->
  forall e1 e2,
    E (open_ty_rec k U T) rs rho e1 e2 <->
    E T (firstn k rs ++ Vb U [] rho :: skipn k rs) rho e1 e2.
Proof.
  intros T rs k U rho Hlen Hlc HUn e1 e2. unfold E. split.
  - intros (w1 & w2 & A1 & A2 & Hm1 & Hm2 & HV).
    exists w1, w2. split; [exact A1 | split; [exact A2 | split;
      [exact Hm1 | split; [exact Hm2 |]]]].
    apply (proj1 (Vb_open_subst T k U rho rs Hlen Hlc HUn w1 w2)); exact HV.
  - intros (w1 & w2 & A1 & A2 & Hm1 & Hm2 & HV).
    exists w1, w2. split; [exact A1 | split; [exact A2 | split;
      [exact Hm1 | split; [exact Hm2 |]]]].
    apply (proj2 (Vb_open_subst T k U rho rs Hlen Hlc HUn w1 w2)); exact HV.
Qed.

(* ----------------------------------------------------------------- *)
(* Auxiliary lemmas for the fundamental theorem                       *)
(* ----------------------------------------------------------------- *)

Lemma In_ctx_atoms : forall Gamma y S x,
  In (y, S) Gamma -> In x (atoms_ty S) -> In x (ctx_atoms Gamma).
Proof.
  intros Gamma. induction Gamma as [| [y' S'] G IH]; intros y S x Hin Hat; simpl in *.
  - inversion Hin.
  - destruct Hin as [Heq | Hin].
    + inversion Heq; subst. apply in_app_iff. left. exact Hat.
    + apply in_app_iff. right. apply (IH y S x); auto.
Qed.

Lemma tmsubst_fv_closed : forall t,
  (forall x, ~ In x (fv_tm t)) -> forall gam, tmsubst_fv gam t = t.
Proof.
  intros t. induction t as [ n | a | T b IH | t1 IH1 t2 IH2 | b IH | a IH T | t1 IH1 t2 IH2 ];
  intros Hc gam; simpl in *.
  - reflexivity.
  - exfalso. apply (Hc a). simpl. auto.
  - f_equal. apply IH. intros x Hx. exact (Hc x Hx).
  - rewrite IH1, IH2; [reflexivity | | ]; intros x Hx; apply (Hc x); apply in_app_iff; auto.
  - f_equal. apply IH. intros x Hx. exact (Hc x Hx).
  - f_equal. apply IH. intros x Hx. exact (Hc x Hx).
  - rewrite IH1, IH2; [reflexivity | | ]; intros x Hx; apply (Hc x); apply in_app_iff; auto.
Qed.

(* ----------------------------------------------------------------- *)
(* Fundamental theorem of the logical relation                        *)
(* ----------------------------------------------------------------- *)

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall (sig1 sig2 : atom -> ty) (rho : tenv) (gam1 gam2 : atom -> tm),
    (forall X, lc_ty_at 0 (sig1 X)) ->
    (forall X, lc_ty_at 0 (sig2 X)) ->
    (forall x, lc_tm_at 0 0 (gam1 x)) ->
    (forall x, lc_tm_at 0 0 (gam2 x)) ->
    (forall x S, In (x, S) Gamma -> E S [] rho (gam1 x) (gam2 x)) ->
    E T [] rho (tmsubst_fv gam1 (tmsubst_ty sig1 t))
              (tmsubst_fv gam2 (tmsubst_ty sig2 t)).
Proof.
  intros Delta Gamma t T H.
  induction H as [ Delta Gamma x T Hlk Hwf
                 | L Delta Gamma T1 t2 T2 Hwf Hprem Hbody
                 | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta Gamma t T Hprem Hbody
                 | Delta Gamma t T U H1 IH1 Hwf
                 | Delta Gamma t1 t2 T H1 IH1 H2 IH2 ];
  intros sig1 sig2 rho gam1 gam2 Hs1 Hs2 Hg1 Hg2 Henv.
  - (* T_Var *) simpl. apply (Henv x T). apply lookup_context_In. exact Hlk.
  - (* T_Abs *)
    assert (HlcT1 : lc_ty_at 0 T1) by (apply wf_ty_lc with (Delta := Delta); exact Hwf).
    assert (Hlcb : lc_tm_at 0 1 t2).
    { assert (Hx : ~ In (fresh_atom L) L) by apply fresh_atom_notin.
      destruct (has_type_lc Delta (update Gamma (fresh_atom L) T1)
                  (open_tm t2 (tm_fvar (fresh_atom L))) T2
                  (Hprem (fresh_atom L) Hx)) as [Hlc _].
      eapply lc_tm_open_tm_inv; [exact Hlc | apply lc_tm_fvar]. }
    assert (Hval1 : value (tm_abs (tysub sig1 T1) (tmsubst_fv gam1 (tmsubst_ty sig1 t2)))).
    { apply v_abs. apply lc_tm_abs.
      - apply (proj2 (lc_ty_tysub sig1 Hs1 0 T1)); exact HlcT1.
      - apply lc_tm_tmsubst_fv; [exact Hg1 |].
        apply (proj2 (lc_tm_tmsubst_ty sig1 Hs1 0 1 t2)); exact Hlcb. }
    assert (Hval2 : value (tm_abs (tysub sig2 T1) (tmsubst_fv gam2 (tmsubst_ty sig2 t2)))).
    { apply v_abs. apply lc_tm_abs.
      - apply (proj2 (lc_ty_tysub sig2 Hs2 0 T1)); exact HlcT1.
      - apply lc_tm_tmsubst_fv; [exact Hg2 |].
        apply (proj2 (lc_tm_tmsubst_ty sig2 Hs2 0 1 t2)); exact Hlcb. }
    simpl.
    unfold E.
    exists (tm_abs (tysub sig1 T1) (tmsubst_fv gam1 (tmsubst_ty sig1 t2))),
           (tm_abs (tysub sig2 T1) (tmsubst_fv gam2 (tmsubst_ty sig2 t2))).
    split; [exact Hval1 | split; [exact Hval2 | split; [apply multi_refl | split; [apply multi_refl |]]]].
    simpl.
    exists (tysub sig1 T1), (tmsubst_fv gam1 (tmsubst_ty sig1 t2)),
           (tysub sig2 T1), (tmsubst_fv gam2 (tmsubst_ty sig2 t2)).
    split; [reflexivity | split; [reflexivity |]].
    intros a1 a2 HVa.
    destruct HVa as (Hva1 & Hva2 & HVb).
    set (x := fresh_atom (L ++ fv_tm t2 ++ ctx_vars Gamma)).
    assert (Hxall : ~ In x (L ++ fv_tm t2 ++ ctx_vars Gamma)).
    { subst x. apply fresh_atom_notin. }
    assert (HxL : ~ In x L).
    { intros Hin. apply Hxall. apply in_app_iff. left. exact Hin. }
    assert (Hxfv : ~ In x (fv_tm t2)).
    { intros Hin. apply Hxall. apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
    assert (HxG : ~ In x (ctx_vars Gamma)).
    { intros Hin. apply Hxall. apply in_app_iff. right. apply in_app_iff. right. exact Hin. }
    assert (Hg1' : forall y, lc_tm_at 0 0 (pfv gam1 x a1 y)).
    { intros y. unfold pfv. destruct (Nat.eqb y x) eqn:E.
      - apply Nat.eqb_eq in E. subst. apply value_lc. exact Hva1.
      - apply Hg1. }
    assert (Hg2' : forall y, lc_tm_at 0 0 (pfv gam2 x a2 y)).
    { intros y. unfold pfv. destruct (Nat.eqb y x) eqn:E.
      - apply Nat.eqb_eq in E. subst. apply value_lc. exact Hva2.
      - apply Hg2. }
    assert (Henv' : forall y S, In (y, S) (update Gamma x T1) ->
            E S [] rho (pfv gam1 x a1 y) (pfv gam2 x a2 y)).
    { intros y S Hin. unfold update in Hin. simpl in Hin.
      destruct Hin as [Heq | Hin].
      - inversion Heq; subst.
        rewrite pfv_same, pfv_same.
        exists a1, a2. split; [exact Hva1 | split; [exact Hva2 | split;
          [apply multi_refl | split; [apply multi_refl | exact HVb]]]].
      - assert (Hne : y <> x).
        { intros ->. apply HxG. apply In_ctx_vars with (T := S). exact Hin. }
        rewrite (pfv_other gam1 x a1 y Hne), (pfv_other gam2 x a2 y Hne).
        apply Henv. exact Hin. }
    specialize (Hbody x HxL sig1 sig2 rho (pfv gam1 x a1) (pfv gam2 x a2)
                  Hs1 Hs2 Hg1' Hg2' Henv').
    unfold open_tm in Hbody.
    rewrite !tmsubst_ty_open_tm in Hbody.
    rewrite (tmsubst_fv_open_tm (pfv gam1 x a1) Hg1') in Hbody.
    rewrite (tmsubst_fv_open_tm (pfv gam2 x a2) Hg2') in Hbody.
    simpl in Hbody.
    rewrite !pfv_same in Hbody.
    rewrite (fv_tm_tmsubst_fv_irrel (tmsubst_ty sig1 t2) (pfv gam1 x a1) gam1) in Hbody.
    2: { intros y Hy. apply pfv_other. intros ->. apply Hxfv.
         apply (proj1 (In_fv_tm_tmsubst_ty x sig1 t2)); exact Hy. }
    rewrite (fv_tm_tmsubst_fv_irrel (tmsubst_ty sig2 t2) (pfv gam2 x a2) gam2) in Hbody.
    2: { intros y Hy. apply pfv_other. intros ->. apply Hxfv.
         apply (proj1 (In_fv_tm_tmsubst_ty x sig2 t2)); exact Hy. }
    simpl in Hbody.
    exact Hbody.
  - (* T_App *)
    destruct (IH1 sig1 sig2 rho gam1 gam2 Hs1 Hs2 Hg1 Hg2 Henv)
      as (w1 & w2 & Hv1 & Hv2 & Hm1 & Hm2 & HV1).
    destruct (IH2 sig1 sig2 rho gam1 gam2 Hs1 Hs2 Hg1 Hg2 Henv)
      as (u1 & u2 & Hu1 & Hu2 & Hn1 & Hn2 & HV2).
    simpl in HV1.
    destruct HV1 as (Ta & b1 & Tb & b2 & E1 & E2 & Hcl).
    subst w1 w2.
    destruct (Hcl u1 u2 (conj Hu1 (conj Hu2 HV2)))
      as (z1 & z2 & Hz1 & Hz2 & Hr1 & Hr2 & HVz).
    destruct (has_type_lc Delta Gamma t2 T1 H2) as (Hlc2 & _).
    assert (Hlcf1 : locally_closed_tm (tmsubst_fv gam1 (tmsubst_ty sig1 t2))).
    { apply lc_tm_tmsubst_fv; [exact Hg1 |].
      apply (proj2 (lc_tm_tmsubst_ty sig1 Hs1 0 0 t2)); exact Hlc2. }
    assert (Hlcf2 : locally_closed_tm (tmsubst_fv gam2 (tmsubst_ty sig2 t2))).
    { apply lc_tm_tmsubst_fv; [exact Hg2 |].
      apply (proj2 (lc_tm_tmsubst_ty sig2 Hs2 0 0 t2)); exact Hlc2. }
    simpl. unfold E.
    exists z1, z2. split; [exact Hz1 | split; [exact Hz2 | split; [| split; [| exact HVz]]]].
    + eapply multi_trans.
      * apply multi_app_l; [exact Hm1 | exact Hlcf1].
      * eapply multi_trans.
        -- apply multi_app_r; [exact Hv1 | exact Hn1].
        -- eapply multi_trans.
           ++ eapply multi_step.
              ** apply ST_AppAbs; [apply value_lc; exact Hv1 | exact Hu1].
              ** apply multi_refl.
           ++ exact Hr1.
    + eapply multi_trans.
      * apply multi_app_l; [exact Hm2 | exact Hlcf2].
      * eapply multi_trans.
        -- apply multi_app_r; [exact Hv2 | exact Hn2].
        -- eapply multi_trans.
           ++ eapply multi_step.
              ** apply ST_AppAbs; [apply value_lc; exact Hv2 | exact Hu2].
              ** apply multi_refl.
           ++ exact Hr2.
  - (* T_TAbs *)
    assert (Hlcb : lc_tm_at 1 0 t).
    { assert (HX : ~ In (fresh_atom L) L) by apply fresh_atom_notin.
      destruct (has_type_lc (fresh_atom L :: Delta) Gamma
                  (open_tm_ty t (Ty_FVar (fresh_atom L)))
                  (open_ty T (Ty_FVar (fresh_atom L)))
                  (Hprem (fresh_atom L) HX)) as [Hlc _].
      apply (lc_tm_open_ty_inv 0 0 (Ty_FVar (fresh_atom L)) t) in Hlc.
      simpl in Hlc. exact Hlc. }
    assert (HlcT : lc_ty_at 1 T).
    { assert (HX : ~ In (fresh_atom L) L) by apply fresh_atom_notin.
      destruct (has_type_lc (fresh_atom L :: Delta) Gamma
                  (open_tm_ty t (Ty_FVar (fresh_atom L)))
                  (open_ty T (Ty_FVar (fresh_atom L)))
                  (Hprem (fresh_atom L) HX)) as [_ HT].
      apply (lc_ty_open_inv 0 (Ty_FVar (fresh_atom L)) T) in HT.
      simpl in HT. exact HT. }
    assert (Hval1 : value (tm_tabs (tmsubst_fv gam1 (tmsubst_ty sig1 t)))).
    { apply v_tabs. apply lc_tm_tabs.
      apply lc_tm_tmsubst_fv; [exact Hg1 |].
      apply (proj2 (lc_tm_tmsubst_ty sig1 Hs1 1 0 t)); exact Hlcb. }
    assert (Hval2 : value (tm_tabs (tmsubst_fv gam2 (tmsubst_ty sig2 t)))).
    { apply v_tabs. apply lc_tm_tabs.
      apply lc_tm_tmsubst_fv; [exact Hg2 |].
      apply (proj2 (lc_tm_tmsubst_ty sig2 Hs2 1 0 t)); exact Hlcb. }
    simpl. unfold E.
    exists (tm_tabs (tmsubst_fv gam1 (tmsubst_ty sig1 t))),
           (tm_tabs (tmsubst_fv gam2 (tmsubst_ty sig2 t))).
    split; [exact Hval1 | split; [exact Hval2 | split; [apply multi_refl | split; [apply multi_refl |]]]].
    simpl.
    exists (tmsubst_fv gam1 (tmsubst_ty sig1 t)), (tmsubst_fv gam2 (tmsubst_ty sig2 t)).
    split; [reflexivity | split; [reflexivity |]].
    intros U1 U2 R HU1 HU2.
    set (x := fresh_atom (L ++ atoms_ty T ++ atoms_tm t ++ ctx_atoms Gamma ++ ctx_vars Gamma)).
    assert (Hxall : ~ In x (L ++ atoms_ty T ++ atoms_tm t ++ ctx_atoms Gamma ++ ctx_vars Gamma)).
    { subst x. apply fresh_atom_notin. }
    assert (HxL : ~ In x L).
    { intros Hin. apply Hxall. apply in_app_iff. left. exact Hin. }
    assert (HxT : ~ In x (atoms_ty T)).
    { intros Hin. apply Hxall. apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
    assert (Hxtm : ~ In x (atoms_tm t)).
    { intros Hin. apply Hxall. apply in_app_iff. right. apply in_app_iff. right.
      apply in_app_iff. left. exact Hin. }
    assert (Hxat : ~ In x (ctx_atoms Gamma)).
    { intros Hin. apply Hxall. apply in_app_iff. right. apply in_app_iff. right.
      apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
    assert (HxG : ~ In x (ctx_vars Gamma)).
    { intros Hin. apply Hxall. apply in_app_iff. right. apply in_app_iff. right.
      apply in_app_iff. right. apply in_app_iff. right. exact Hin. }
    assert (Hs1' : forall X, lc_ty_at 0 (pty sig1 x U1 X)).
    { intros X. unfold pty. destruct (Nat.eqb X x) eqn:E.
      - exact HU1. - apply Nat.eqb_neq in E. apply Hs1. }
    assert (Hs2' : forall X, lc_ty_at 0 (pty sig2 x U2 X)).
    { intros X. unfold pty. destruct (Nat.eqb X x) eqn:E.
      - exact HU2. - apply Nat.eqb_neq in E. apply Hs2. }
    assert (Henv' : forall y S, In (y, S) Gamma ->
            E S [] (extend rho x R) (gam1 y) (gam2 y)).
    { intros y S Hin.
      assert (Hag : forall X, In X (atoms_ty S) ->
                    forall w1 w2, extend rho x R X w1 w2 <-> rho X w1 w2).
      { intros X HX w1 w2. rewrite extend_other; [tauto |].
        intros ->. apply Hxat. apply In_ctx_atoms with (y := y) (S := S); auto. }
      exact (proj2 (E_env_cong S [] (extend rho x R) rho Hag (gam1 y) (gam2 y))
                   (Henv y S Hin)). }
    specialize (Hbody x HxL (pty sig1 x U1) (pty sig2 x U2) (extend rho x R)
                  gam1 gam2 Hs1' Hs2' Hg1 Hg2 Henv').
    unfold open_tm_ty in Hbody.
    rewrite (tmsubst_ty_point_open sig1 x U1 t Hs1 HU1 Hxtm) in Hbody.
    rewrite (tmsubst_ty_point_open sig2 x U2 t Hs2 HU2 Hxtm) in Hbody.
    rewrite (tmsubst_fv_open_tm_ty gam1 Hg1) in Hbody.
    rewrite (tmsubst_fv_open_tm_ty gam2 Hg2) in Hbody.
    exact (proj1 (E_open_atom T [] 0 x R rho eq_refl HlcT HxT
                    (open_tm_ty (tmsubst_fv gam1 (tmsubst_ty sig1 t)) U1)
                    (open_tm_ty (tmsubst_fv gam2 (tmsubst_ty sig2 t)) U2)) Hbody).
  - (* T_TApp *)
    destruct (IH1 sig1 sig2 rho gam1 gam2 Hs1 Hs2 Hg1 Hg2 Henv)
      as (w1 & w2 & Hv1 & Hv2 & Hm1 & Hm2 & HV).
    simpl in HV.
    destruct HV as (b1 & b2 & E1 & E2 & Hcl).
    subst w1 w2.
    assert (HlcU : lc_ty_at 0 U) by (apply wf_ty_lc with (Delta := Delta); exact Hwf).
    assert (HlcU1 : lc_ty_at 0 (tysub sig1 U)).
    { apply (proj2 (lc_ty_tysub sig1 Hs1 0 U)); exact HlcU. }
    assert (HlcU2 : lc_ty_at 0 (tysub sig2 U)).
    { apply (proj2 (lc_ty_tysub sig2 Hs2 0 U)); exact HlcU. }
    assert (HlcT : lc_ty_at 1 T).
    { destruct (has_type_lc Delta Gamma t (Ty_All T) H1) as [_ HT].
      apply lc_ty_all_inv in HT. exact HT. }
    destruct (Hcl (tysub sig1 U) (tysub sig2 U) (Vb U [] rho) HlcU1 HlcU2)
      as (z1 & z2 & Hz1 & Hz2 & Hr1 & Hr2 & HVz).
    simpl. unfold E.
    exists z1, z2. split; [exact Hz1 | split; [exact Hz2 | split; [| split; [|]]]].
    + eapply multi_trans.
      * eapply multi_trans.
        -- apply multi_tapp; [exact Hm1 | exact HlcU1].
        -- eapply multi_step.
           ++ apply ST_TAppTabs; [apply value_lc; exact Hv1 | exact HlcU1].
           ++ apply multi_refl.
      * exact Hr1.
    + eapply multi_trans.
      * eapply multi_trans.
        -- apply multi_tapp; [exact Hm2 | exact HlcU2].
        -- eapply multi_step.
           ++ apply ST_TAppTabs; [apply value_lc; exact Hv2 | exact HlcU2].
           ++ apply multi_refl.
      * exact Hr2.
    + exact (proj2 (Vb_open_subst T 0 U rho [] eq_refl HlcT HlcU z1 z2) HVz).
  - (* T_Choice *)
    destruct (IH1 sig1 sig2 rho gam1 gam2 Hs1 Hs2 Hg1 Hg2 Henv)
      as (w1 & w2 & Hv1 & Hv2 & Hm1 & Hm2 & HV).
    destruct (has_type_lc Delta Gamma t1 T H1) as (Hlc1 & _).
    destruct (has_type_lc Delta Gamma t2 T H2) as (Hlc2 & _).
    assert (HlcI1 : locally_closed_tm (tmsubst_fv gam1 (tmsubst_ty sig1 t1))).
    { apply lc_tm_tmsubst_fv; [exact Hg1 |].
      apply (proj2 (lc_tm_tmsubst_ty sig1 Hs1 0 0 t1)); exact Hlc1. }
    assert (HlcI2 : locally_closed_tm (tmsubst_fv gam1 (tmsubst_ty sig1 t2))).
    { apply lc_tm_tmsubst_fv; [exact Hg1 |].
      apply (proj2 (lc_tm_tmsubst_ty sig1 Hs1 0 0 t2)); exact Hlc2. }
    assert (HlcJ1 : locally_closed_tm (tmsubst_fv gam2 (tmsubst_ty sig2 t1))).
    { apply lc_tm_tmsubst_fv; [exact Hg2 |].
      apply (proj2 (lc_tm_tmsubst_ty sig2 Hs2 0 0 t1)); exact Hlc1. }
    assert (HlcJ2 : locally_closed_tm (tmsubst_fv gam2 (tmsubst_ty sig2 t2))).
    { apply lc_tm_tmsubst_fv; [exact Hg2 |].
      apply (proj2 (lc_tm_tmsubst_ty sig2 Hs2 0 0 t2)); exact Hlc2. }
    simpl. unfold E.
    exists w1, w2. split; [exact Hv1 | split; [exact Hv2 | split; [| split; [| exact HV]]]].
    + eapply multi_trans.
      * eapply multi_step.
        -- apply ST_ChoiceLeft; [exact HlcI1 | exact HlcI2].
        -- apply multi_refl.
      * exact Hm1.
    + eapply multi_trans.
      * eapply multi_step.
        -- apply ST_ChoiceRight; [exact HlcJ1 | exact HlcJ2].
        -- apply multi_refl.
      * exact Hm2.
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
