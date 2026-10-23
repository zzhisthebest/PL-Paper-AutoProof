(** System F parametricity benchmark, Hard variant.
    Features: none. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityNoneHardTask.

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

  | tm_tapp : tm -> ty -> tm.

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
  end.

Fixpoint tm_subst (x : atom) (s t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => if Nat.eqb x y then s else tm_fvar y
  | tm_abs T t1 => tm_abs T (tm_subst x s t1)
  | tm_app t1 t2 => tm_app (tm_subst x s t1) (tm_subst x s t2)
  | tm_tabs t1 => tm_tabs (tm_subst x s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst x s t1) T
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
      lc_tm_at K k (tm_tapp t T).

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
      has_type Delta Gamma (tm_tapp t U) (open_ty T U).

Lemma wf_ty_mono : forall Delta T,
  wf_ty Delta T -> forall Delta', incl Delta Delta' -> wf_ty Delta' T.
Proof.
  intros Delta T H; induction H; intros Delta' Hinc.
  - apply WF_Var. apply Hinc. exact H.
  - apply WF_Arrow; eauto.
  - eapply WF_All with (L := L). intros X HX.
    apply H0; [exact HX|].
    intros Y HY. simpl. destruct HY as [<-|HY].
    + now left.
    + right. apply Hinc. exact HY.
Qed.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).


Hint Constructors lc_ty_at lc_tm_at value : core.

(* The binary interpretation used below relates closed values.  The list
   records interpretations of locally nameless type variables; free type
   variables are interpreted by [xi]. *)
Definition value_relation := tm -> tm -> Prop.

Fixpoint value_rel (rho : list value_relation)
    (xi : atom -> value_relation) (T : ty) : value_relation :=
  match T with
  | Ty_BVar i => fun v1 v2 =>
      match nth_error rho i with
      | Some R => R v1 v2
      | None => False
      end
  | Ty_FVar X => xi X
  | Ty_Arrow A B => fun f g =>
      forall a b, value a -> value b -> value_rel rho xi A a b ->
        exists r s, multi (tm_app f a) r /\ multi (tm_app g b) s /\
                    value r /\ value s /\ value_rel rho xi B r s
  | Ty_All A => fun f g =>
      forall U V R,
        wf_ty [] U -> wf_ty [] V ->
        exists r s, multi (tm_tapp f U) r /\ multi (tm_tapp g V) s /\
                    value r /\ value s /\
                    value_rel (R :: rho) xi A r s
  end.

Definition term_rel (rho : list value_relation)
    (xi : atom -> value_relation) (T : ty) (t1 t2 : tm) : Prop :=
  exists v1 v2, multi t1 v1 /\ multi t2 v2 /\
                value v1 /\ value v2 /\ value_rel rho xi T v1 v2.

Definition term_context_rel (rho : list value_relation)
    (xi : atom -> value_relation) (Gamma : context)
    (sigma1 sigma2 : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    value (sigma1 x) /\ value (sigma2 x) /\
    value_rel rho xi T (sigma1 x) (sigma2 x).

Fixpoint instantiate_tm (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T t1 => tm_abs T (instantiate_tm sigma t1)
  | tm_app t1 t2 => tm_app (instantiate_tm sigma t1) (instantiate_tm sigma t2)
  | tm_tabs t1 => tm_tabs (instantiate_tm sigma t1)
  | tm_tapp t1 T => tm_tapp (instantiate_tm sigma t1) T
  end.

Fixpoint substitute_type_vars (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (substitute_type_vars theta A)
                              (substitute_type_vars theta B)
  | Ty_All A => Ty_All (substitute_type_vars theta A)
  end.

Fixpoint substitute_tm_type_vars (theta : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (substitute_type_vars theta T)
                         (substitute_tm_type_vars theta b)
  | tm_app a b => tm_app (substitute_tm_type_vars theta a)
                          (substitute_tm_type_vars theta b)
  | tm_tabs b => tm_tabs (substitute_tm_type_vars theta b)
  | tm_tapp a T => tm_tapp (substitute_tm_type_vars theta a)
                            (substitute_type_vars theta T)
  end.

Definition update_type_subst (theta : atom -> ty) (X : atom) (U : ty) :=
  fun Y => if Nat.eqb Y X then U else theta Y.

Definition type_context_rel (Delta : ty_context)
    (theta1 theta2 : atom -> ty) (xi : atom -> value_relation) : Prop :=
  forall X, In X Delta -> wf_ty [] (theta1 X) /\ wf_ty [] (theta2 X).

Lemma type_context_rel_update : forall Delta theta1 theta2 xi X U V,
  ~ In X Delta ->
  type_context_rel Delta theta1 theta2 xi ->
  wf_ty [] U -> wf_ty [] V ->
  type_context_rel (X :: Delta)
    (update_type_subst theta1 X U) (update_type_subst theta2 X V) xi.
Proof.
  intros Delta theta1 theta2 xi X U V HX Henv HU HV Y Hin.
  simpl in Hin. destruct Hin as [<-|Hin].
  - unfold update_type_subst. rewrite Nat.eqb_refl. auto.
  - assert (Y <> X) by (intro E; subst; contradiction).
    unfold update_type_subst.
    destruct (Nat.eqb Y X) eqn:E.
    + apply Nat.eqb_eq in E; contradiction.
    +
    apply Henv. exact Hin.
Qed.

Fixpoint ty_fvars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fvars A ++ ty_fvars B
  | Ty_All A => ty_fvars A
  end.

Definition context_fvars (Gamma : context) : list atom :=
  concat (map (fun p => ty_fvars (snd p)) Gamma).

Fixpoint tm_ty_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ => []
  | tm_abs T b => ty_fvars T ++ tm_ty_fvars b
  | tm_app a b => tm_ty_fvars a ++ tm_ty_fvars b
  | tm_tabs b => tm_ty_fvars b
  | tm_tapp a T => tm_ty_fvars a ++ ty_fvars T
  end.

Lemma substitute_type_update_absent : forall T theta X U,
  ~ In X (ty_fvars T) ->
  substitute_type_vars (update_type_subst theta X U) T =
  substitute_type_vars theta T.
Proof.
  induction T; intros theta X U Hfresh; simpl in *.
  - reflexivity.
  - assert (X <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold update_type_subst. destruct (Nat.eqb a X) eqn:E.
    + apply Nat.eqb_eq in E; congruence.
    + reflexivity.
  - assert (H1 : ~ In X (ty_fvars T1)).
    { intro Hin; apply Hfresh; apply in_or_app; now left. }
    assert (H2 : ~ In X (ty_fvars T2)).
    { intro Hin; apply Hfresh; apply in_or_app; now right. }
    rewrite IHT1 by exact H1. rewrite IHT2 by exact H2. reflexivity.
  - rewrite IHT by exact Hfresh. reflexivity.
Qed.

Lemma substitute_tm_type_update_absent : forall t theta X U,
  ~ In X (tm_ty_fvars t) ->
  substitute_tm_type_vars (update_type_subst theta X U) t =
  substitute_tm_type_vars theta t.
Proof.
  induction t as [i|x|A b IH|a IHa c IHc|b IH|a IHa A];
    intros theta X U Hfresh; simpl in *; try reflexivity.
  - assert (HT : ~ In X (ty_fvars A)).
    { intro Hin; apply Hfresh; apply in_or_app; now left. }
    assert (HB : ~ In X (tm_ty_fvars b)).
    { intro Hin; apply Hfresh; apply in_or_app; now right. }
    rewrite substitute_type_update_absent by exact HT.
    rewrite IH by exact HB. reflexivity.
  - assert (H1 : ~ In X (tm_ty_fvars a)).
    { intro Hin; apply Hfresh; apply in_or_app; now left. }
    assert (H2 : ~ In X (tm_ty_fvars c)).
    { intro Hin; apply Hfresh; apply in_or_app; now right. }
    rewrite IHa by exact H1. rewrite IHc by exact H2. reflexivity.
  - f_equal. apply IH. exact Hfresh.
  - assert (HA : ~ In X (tm_ty_fvars a)).
    { intro Hin; apply Hfresh; apply in_or_app; now left. }
    assert (HT : ~ In X (ty_fvars A)).
    { intro Hin; apply Hfresh; apply in_or_app; now right. }
    rewrite IHa by exact HA. rewrite substitute_type_update_absent by exact HT.
    reflexivity.
Qed.

Definition context_vars (Gamma : context) : list atom := map fst Gamma.

Definition update_tm_subst (sigma : atom -> tm) (x : atom) (v : tm) :=
  fun y => if Nat.eqb y x then v else sigma y.

Fixpoint tm_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b | tm_tabs b => tm_fvars b
  | tm_app a b => tm_fvars a ++ tm_fvars b
  | tm_tapp a _ => tm_fvars a
  end.

Lemma instantiate_update_absent : forall t sigma x a,
  ~ In x (tm_fvars t) ->
  instantiate_tm (update_tm_subst sigma x a) t = instantiate_tm sigma t.
Proof.
  induction t as [i|y|A b IH|a0 IHa b IHb|b IH|a0 IHa T];
    intros sigma x a Hfresh; simpl in *; try reflexivity.
  - assert (x <> y) by (intro E; subst; apply Hfresh; simpl; auto).
    unfold update_tm_subst. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E; congruence.
    + reflexivity.
  - f_equal. apply IH. exact Hfresh.
  - assert (H1 : ~ In x (tm_fvars a0)).
    { intro Hin; apply Hfresh; apply in_or_app; now left. }
    assert (H2 : ~ In x (tm_fvars b)).
    { intro Hin; apply Hfresh; apply in_or_app; now right. }
    rewrite IHa by exact H1. rewrite IHb by exact H2. reflexivity.
  - f_equal. apply IH. exact Hfresh.
  - f_equal. apply IHa. exact Hfresh.
Qed.

Lemma context_fvars_absent : forall Gamma X,
  ~ In X (context_fvars Gamma) ->
  forall x T, In (x,T) Gamma -> ~ In X (ty_fvars T).
Proof.
  induction Gamma as [|[y S] Gamma IH]; intros X Hfresh x T Hin; [contradiction|].
  simpl in Hfresh. simpl in Hin.
  destruct Hin as [E|Hin].
  - inversion E; subst. intro HX. apply Hfresh. apply in_or_app; now left.
  - apply IH with (x:=x) (T:=T); [|exact Hin].
    intro HX. apply Hfresh. apply in_or_app; now right.
Qed.

Lemma lookup_context_in : forall Gamma x T,
  lookup_context x Gamma = Some T -> In (x,T) Gamma.
Proof.
  induction Gamma as [|[y S] Gamma IH]; intros x T H; simpl in H.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion H; subst. left. apply Nat.eqb_eq in E. now subst.
    + right. apply IH. exact H.
Qed.

Lemma lookup_context_update_same : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros; simpl. now rewrite Nat.eqb_refl. Qed.

Lemma lookup_context_update_other : forall Gamma x y T,
  x <> y -> lookup_context x (update Gamma y T) = lookup_context x Gamma.
Proof.
  intros; simpl. destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; contradiction.
  - reflexivity.
Qed.

Definition update_rel (xi : atom -> value_relation) (X : atom)
    (R : value_relation) := fun Y => if Nat.eqb Y X then R else xi Y.

Lemma update_rel_same : forall xi X R, update_rel xi X R X = R.
Proof. intros; unfold update_rel; now rewrite Nat.eqb_refl. Qed.

Lemma update_rel_other : forall xi X Y R,
  X <> Y -> update_rel xi X R Y = xi Y.
Proof.
  intros; unfold update_rel. destruct (Nat.eqb Y X) eqn:E; auto.
  apply Nat.eqb_eq in E; congruence.
Qed.

Lemma term_context_rel_update : forall rho xi Gamma sigma1 sigma2 x T a b,
  ~ In x (context_vars Gamma) ->
  term_context_rel rho xi Gamma sigma1 sigma2 ->
  value a -> value b -> value_rel rho xi T a b ->
  term_context_rel rho xi (update Gamma x T)
    (update_tm_subst sigma1 x a) (update_tm_subst sigma2 x b).
Proof.
  intros rho xi Gamma sigma1 sigma2 x T a b Hfresh Henv Ha Hb Hab.
  intros y S Hlookup. unfold update_tm_subst.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E; subst y. rewrite lookup_context_update_same in Hlookup.
    inversion Hlookup; subst S. simpl. repeat split; assumption.
  - apply Nat.eqb_neq in E.
    rewrite lookup_context_update_other in Hlookup by congruence.
    specialize (Henv y S Hlookup).
    exact Henv.
Qed.

Fixpoint insert_relation (k : nat) (R : value_relation)
    (rho : list value_relation) : list value_relation :=
  match k with
  | 0 => R :: rho
  | S n => match rho with
           | [] => []
           | Q :: rho' => Q :: insert_relation n R rho'
           end
  end.

Lemma nth_error_insert_before : forall k R rho i,
  i < k -> nth_error (insert_relation k R rho) i = nth_error rho i.
Proof.
  induction k; intros R rho i H; [lia|].
  destruct rho as [|Q rho']; simpl.
  - reflexivity.
  - destruct i; simpl; [reflexivity|]. apply IHk. lia.
Qed.

Lemma nth_error_insert_at : forall k R rho,
  k <= length rho ->
  nth_error (insert_relation k R rho) k = Some R.
Proof.
  induction k; intros R rho Hlen; simpl; [reflexivity|].
  destruct rho as [|Q rho']; simpl in *; [lia|].
  rewrite IHk; [reflexivity|]. lia.
Qed.

Lemma value_rel_open_type : forall T k,
  lc_ty_at (S k) T ->
  forall rho xi X R v1 v2,
    ~ In X (ty_fvars T) ->
    k <= length rho ->
    value_rel (insert_relation k R rho) (update_rel xi X R)
      (open_ty_rec k (Ty_FVar X) T) v1 v2 <->
    value_rel (insert_relation k R rho) xi T v1 v2.
Proof.
  induction T; intros k Hlc rho xi X R v1 v2 Hfresh Hlen; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      rewrite nth_error_insert_at by assumption.
      unfold update_rel. destruct (Nat.eqb X X) eqn:E.
      * change (update_rel xi X R X v1 v2 <-> R v1 v2).
        unfold update_rel. rewrite Nat.eqb_refl. tauto.
      * apply Nat.eqb_neq in E. contradiction.
    + apply Nat.eqb_neq in E.
      assert (n < k) by lia.
      cbn [value_rel]. rewrite nth_error_insert_before by assumption. reflexivity.
  - assert (X <> a) as Hneq.
    { intro Heq; subst. apply Hfresh. simpl; auto. }
    rewrite update_rel_other by congruence. tauto.
  - inversion Hlc; subst.
    assert (HF1 : ~ In X (ty_fvars T1)).
    { intro Hin. apply Hfresh. apply in_or_app; now left. }
    assert (HF2 : ~ In X (ty_fvars T2)).
    { intro Hin. apply Hfresh. apply in_or_app; now right. }
    split; intros H a b Hva Hvb Hab.
    + destruct (H a b Hva Hvb) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      * apply (proj2 (IHT1 k H2 rho xi X R a b HF1 Hlen)); exact Hab.
      * exists r, s. repeat split; try assumption.
        apply (proj1 (IHT2 k H3 rho xi X R r s HF2 Hlen)); exact Hrel.
    + destruct (H a b Hva Hvb) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      * apply (proj1 (IHT1 k H2 rho xi X R a b HF1 Hlen)); exact Hab.
      * exists r, s. repeat split; try assumption.
        apply (proj2 (IHT2 k H3 rho xi X R r s HF2 Hlen)); exact Hrel.
  - assert (Hbody : lc_ty_at (S (S k)) T).
    { inversion Hlc; assumption. }
    split; intros H U V Q HU HV.
    + specialize (H U V Q HU HV).
      destruct H as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      exists r, s. repeat split; try assumption.
      apply (proj1 (IHT (S k) Hbody (Q :: rho) xi X R r s
        Hfresh ltac:(simpl; lia))); exact Hrel.
    + specialize (H U V Q HU HV).
      destruct H as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      exists r, s. repeat split; try assumption.
      apply (proj2 (IHT (S k) Hbody (Q :: rho) xi X R r s
        Hfresh ltac:(simpl; lia))); exact Hrel.
Qed.

Lemma value_rel_update_absent : forall T,
  forall rho xi X R,
  ~ In X (ty_fvars T) ->
  forall v1 v2,
    value_rel rho (update_rel xi X R) T v1 v2 <->
    value_rel rho xi T v1 v2.
Proof.
  induction T; intros rho xi X R Hfresh v1 v2; simpl in *.
  - tauto.
  - assert (X <> a) by (intro E; subst; apply Hfresh; simpl; auto).
    rewrite update_rel_other by congruence. tauto.
  - assert (HF1 : ~ In X (ty_fvars T1)).
    { intro Hin; apply Hfresh; apply in_or_app; now left. }
    assert (HF2 : ~ In X (ty_fvars T2)).
    { intro Hin; apply Hfresh; apply in_or_app; now right. }
    split; intros H a b Hva Hvb Hab.
    + destruct (H a b Hva Hvb) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      * apply (proj2 (IHT1 rho xi X R HF1 a b)); exact Hab.
      * exists r,s. repeat split; try assumption.
        apply (proj1 (IHT2 rho xi X R HF2 r s)); exact Hrel.
    + destruct (H a b Hva Hvb) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      * apply (proj1 (IHT1 rho xi X R HF1 a b)); exact Hab.
      * exists r,s. repeat split; try assumption.
        apply (proj2 (IHT2 rho xi X R HF2 r s)); exact Hrel.
  - split; intros H U V S HU HV.
    + destruct (H U V S HU HV) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      exists r,s. repeat split; try assumption.
      apply (proj1 (IHT (S :: rho) xi X R Hfresh r s)); exact Hrel.
    + destruct (H U V S HU HV) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      exists r,s. repeat split; try assumption.
      apply (proj2 (IHT (S :: rho) xi X R Hfresh r s)); exact Hrel.
Qed.

Definition relation_env_agree (k : nat) (rho1 rho2 : list value_relation) : Prop :=
  forall i, i < k ->
    match nth_error rho1 i, nth_error rho2 i with
    | Some R1, Some R2 => forall a b, R1 a b <-> R2 a b
    | None, None => True
    | _, _ => False
    end.

Lemma value_rel_env_irrelevant : forall T k,
  lc_ty_at k T ->
  forall rho1 rho2 xi v1 v2,
    relation_env_agree k rho1 rho2 ->
    (value_rel rho1 xi T v1 v2 <-> value_rel rho2 xi T v1 v2).
Proof.
  induction T; intros k Hlc rho1 rho2 xi v1 v2 Hagree; simpl in *.
  - inversion Hlc; subst.
    destruct (nth_error rho1 n) as [R1|] eqn:E1;
      destruct (nth_error rho2 n) as [R2|] eqn:E2; simpl.
    + specialize (Hagree n H1). rewrite E1, E2 in Hagree. simpl in Hagree.
      apply (Hagree v1 v2).
    + specialize (Hagree n H1). rewrite E1, E2 in Hagree. simpl in Hagree. contradiction.
    + specialize (Hagree n H1). rewrite E1, E2 in Hagree. simpl in Hagree. contradiction.
    + tauto.
  - tauto.
  - inversion Hlc; subst. split; intros H a b Hva Hvb Hab.
    + destruct (H a b Hva Hvb) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      * apply (proj2 (IHT1 k H2 rho1 rho2 xi a b Hagree)); exact Hab.
      * exists r,s. repeat split; try assumption.
        apply (proj1 (IHT2 k H3 rho1 rho2 xi r s Hagree)); exact Hrel.
    + destruct (H a b Hva Hvb) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      * apply (proj1 (IHT1 k H2 rho1 rho2 xi a b Hagree)); exact Hab.
      * exists r,s. repeat split; try assumption.
        apply (proj2 (IHT2 k H3 rho1 rho2 xi r s Hagree)); exact Hrel.
  - inversion Hlc; subst. split; intros H U V R HU HV.
    + destruct (H U V R HU HV) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      exists r,s. repeat split; try assumption.
      apply (proj1 (IHT (S k) H1 (R :: rho1) (R :: rho2) xi r s
        ltac:(intros i Hi; destruct i; simpl; [firstorder|apply Hagree; lia]))).
      exact Hrel.
    + destruct (H U V R HU HV) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      exists r,s. repeat split; try assumption.
      apply (proj2 (IHT (S k) H1 (R :: rho1) (R :: rho2) xi r s
        ltac:(intros i Hi; destruct i; simpl; [firstorder|apply Hagree; lia]))).
      exact Hrel.
Qed.

Lemma relation_env_open_substitute_agree : forall k R rho xi U,
  locally_closed_ty U -> k <= length rho ->
  relation_env_agree (S (S k))
    (R :: insert_relation k (value_rel rho xi U) rho)
    (insert_relation (S k) (value_rel (R :: rho) xi U) (R :: rho)).
Proof.
  intros k R rho xi U HU Hlen i Hi.
  destruct i as [|j].
  - simpl. intros a b. tauto.
  - simpl. assert (Hj : j <= k) by lia.
    destruct (Nat.lt_ge_cases j k) as [Hlt|Hge].
    + rewrite nth_error_insert_before by exact Hlt.
      rewrite nth_error_insert_before by exact Hlt.
      destruct (nth_error rho j); simpl; [intros a b; tauto|exact I].
    + assert (j = k) by lia. subst j.
      rewrite nth_error_insert_at by exact Hlen.
      rewrite nth_error_insert_at by (simpl; lia).
      intros a b.
      exact (value_rel_env_irrelevant U 0 HU rho (R :: rho) xi a b
        ltac:(intros n Hn; lia)).
Qed.

Lemma lc_ty_weaken : forall T k,
  lc_ty_at k T -> lc_ty_at (S k) T.
Proof.
  intros T k H; induction H; eauto using lc_ty_at; try lia.
Qed.

Lemma lc_ty_weaken_to : forall T k,
  locally_closed_ty T -> lc_ty_at k T.
Proof.
  intros T k H; induction k; [exact H|].
  apply lc_ty_weaken. apply IHk.
Qed.

Lemma open_ty_rec_lc_preserve : forall T k U,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  lc_ty_at (S k) (open_ty_rec k U T).
Proof.
  induction T; intros k U Hlc HU; simpl in *.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E.
    + apply lc_ty_weaken_to. exact HU.
    + constructor. inversion Hlc; subst. lia.
  - constructor.
  - inversion Hlc; subst. constructor.
    + eapply IHT1; eassumption.
    + eapply IHT2; eassumption.
  - inversion Hlc; subst. constructor. eapply IHT; eassumption.
Qed.

Lemma value_rel_open_substitute : forall T k,
  lc_ty_at (S k) T ->
  forall rho xi U v1 v2,
    locally_closed_ty U ->
    k <= length rho ->
    value_rel rho xi (open_ty_rec k U T) v1 v2 <->
    value_rel (insert_relation k (value_rel rho xi U) rho) xi T v1 v2.
Proof.
  induction T; intros k Hlc rho xi U v1 v2 HU Hlen; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. rewrite nth_error_insert_at by exact Hlen.
      reflexivity.
    + apply Nat.eqb_neq in E. assert (n < k) by lia.
      cbn [value_rel]. rewrite nth_error_insert_before by assumption. reflexivity.
  - reflexivity.
  - inversion Hlc; subst. split; intros H a b Hva Hvb Hab.
    + destruct (H a b Hva Hvb) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      * apply (proj2 (IHT1 k H2 rho xi U a b HU Hlen)); exact Hab.
      * exists r,s. repeat split; try assumption.
        apply (proj1 (IHT2 k H3 rho xi U r s HU Hlen)); exact Hrel.
    + destruct (H a b Hva Hvb) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      * apply (proj1 (IHT1 k H2 rho xi U a b HU Hlen)); exact Hab.
      * exists r,s. repeat split; try assumption.
        apply (proj2 (IHT2 k H3 rho xi U r s HU Hlen)); exact Hrel.
  - assert (Hbody : lc_ty_at (S (S k)) T).
    { inversion Hlc; assumption. }
    split; intros H U1 V1 R HU1 HV1.
    + destruct (H U1 V1 R HU1 HV1) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      exists r,s. repeat split; try assumption.
      pose proof (relation_env_open_substitute_agree k R rho xi U HU Hlen) as Hagree.
      apply (proj2 (value_rel_env_irrelevant T (S (S k)) Hbody
        (R :: insert_relation k (value_rel rho xi U) rho)
        (insert_relation (S k) (value_rel (R :: rho) xi U) (R :: rho)) xi r s Hagree)).
      apply (proj1 (IHT (S k) Hbody (R :: rho) xi U r s HU ltac:(simpl; lia))).
      exact Hrel.
    + destruct (H U1 V1 R HU1 HV1) as [r [s [Hr [Hs [Hvr [Hvs Hrel]]]]]].
      exists r,s. repeat split; try assumption.
      pose proof (relation_env_open_substitute_agree k R rho xi U HU Hlen) as Hagree.
      apply (proj2 (IHT (S k) Hbody (R :: rho) xi U r s HU ltac:(simpl; lia))).
      apply (proj1 (value_rel_env_irrelevant T (S (S k)) Hbody
        (R :: insert_relation k (value_rel rho xi U) rho)
        (insert_relation (S k) (value_rel (R :: rho) xi U) (R :: rho)) xi r s Hagree)).
      exact Hrel.
Qed.

Lemma term_context_rel_update_relation : forall rho xi Gamma sigma1 sigma2 X R,
  ~ In X (context_fvars Gamma) ->
  term_context_rel rho xi Gamma sigma1 sigma2 ->
  term_context_rel rho (update_rel xi X R) Gamma sigma1 sigma2.
Proof.
  intros rho xi Gamma sigma1 sigma2 X R Hfresh Henv y T Hlookup.
  specialize (Henv y T Hlookup).
  destruct Henv as [Hv1 [Hv2 Hrel]]. repeat split; try assumption.
  apply (proj2 (value_rel_update_absent T rho xi X R
    (context_fvars_absent Gamma X Hfresh y T
      (lookup_context_in Gamma y T Hlookup)) (sigma1 y) (sigma2 y))).
  exact Hrel.
Qed.

Lemma open_tm_rec_lc : forall t K k u,
  lc_tm_at K k t -> open_tm_rec k u t = t.
Proof.
  induction t; intros K k u Hlc; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHt; eassumption.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion Hlc; subst. f_equal. eapply IHt; eassumption.
  - inversion Hlc; subst. f_equal. eapply IHt; eassumption.
Qed.

Lemma lc_tm_weaken : forall t K k,
  lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros t K k H; induction H; eauto using lc_tm_at; try lia.
Qed.

Lemma lc_tm_weaken_to : forall t K k,
  lc_tm_at K 0 t -> lc_tm_at K k t.
Proof.
  intros t K k H; induction k; [exact H|].
  apply lc_tm_weaken. apply IHk.
Qed.

Lemma instantiate_open_tm_rec : forall t k u sigma,
  (forall x, locally_closed_tm (sigma x)) ->
  instantiate_tm sigma (open_tm_rec k u t) =
  open_tm_rec k (instantiate_tm sigma u) (instantiate_tm sigma t).
Proof.
  induction t; intros k u sigma Hsig; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite (open_tm_rec_lc (sigma a) 0 k (instantiate_tm sigma u)).
    + reflexivity.
    + apply lc_tm_weaken_to. apply Hsig.
  - f_equal. apply IHt. exact Hsig.
  - rewrite (IHt1 k u sigma Hsig), (IHt2 k u sigma Hsig). reflexivity.
  - f_equal. apply IHt. exact Hsig.
  - f_equal. apply IHt. exact Hsig.
Qed.

Lemma instantiate_open_tm : forall t u sigma,
  (forall x, locally_closed_tm (sigma x)) ->
  instantiate_tm sigma (open_tm t u) =
  open_tm (instantiate_tm sigma t) (instantiate_tm sigma u).
Proof. intros; apply instantiate_open_tm_rec; assumption. Qed.




Lemma lc_tm_weaken_type : forall t K k,
  lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros t K k H; induction H; eauto using lc_tm_at, lc_ty_weaken.
Qed.

Lemma lc_tm_weaken_type_to : forall t K k,
  locally_closed_tm t -> lc_tm_at K k t.
Proof.
  intros t K k H.
  assert (Htype : lc_tm_at K 0 t).
  { induction K; [exact H|]. apply lc_tm_weaken_type. exact IHK. }
  induction k; [exact Htype|]. apply lc_tm_weaken. exact IHk.
Qed.

Lemma substitute_type_vars_lc : forall T K,
  lc_ty_at K T ->
  forall theta, (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at K (substitute_type_vars theta T).
Proof.
  induction T; intros K Hlc theta Htheta; simpl in *.
  - inversion Hlc; subst. constructor. assumption.
  - apply lc_ty_weaken_to. apply Htheta.
  - inversion Hlc; subst. constructor.
    + eapply IHT1; eassumption.
    + eapply IHT2; eassumption.
  - inversion Hlc; subst. constructor. eapply IHT; eassumption.
Qed.

Lemma substitute_tm_type_vars_lc : forall t K k,
  lc_tm_at K k t ->
  forall theta, (forall X, locally_closed_ty (theta X)) ->
  lc_tm_at K k (substitute_tm_type_vars theta t).
Proof.
  induction t; intros K k Hlc theta Htheta; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - inversion Hlc; subst. constructor; assumption.
  - inversion Hlc; subst. constructor.
    + eapply substitute_type_vars_lc; eauto.
    + eapply IHt; eassumption.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
  - inversion Hlc; subst. constructor. eapply IHt; eassumption.
  - inversion Hlc; subst. constructor.
    + eapply IHt; eassumption.
    + eapply substitute_type_vars_lc; eauto.
Qed.

Lemma instantiate_tm_lc : forall t K k (sigma : atom -> tm),
  lc_tm_at K k t ->
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k (instantiate_tm sigma t).
Proof.
  induction t; intros K k sigma Hlc Hsigma; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - apply lc_tm_weaken_type_to. apply lc_tm_weaken_to. apply Hsigma.
  - inversion Hlc; subst. constructor; [assumption|].
    eapply IHt; eassumption.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
  - inversion Hlc; subst. constructor. eapply IHt; eassumption.
  - inversion Hlc; subst. constructor.
    + eapply IHt; eassumption.
    + assumption.
Qed.

Lemma open_ty_rec_lc_noop : forall T k U,
  lc_ty_at k T -> open_ty_rec k U T = T.
Proof.
  induction T; intros k U H; simpl.
  - inversion H; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - inversion H; subst. f_equal; eauto.
  - inversion H; subst. f_equal. eapply IHT. eassumption.
Qed.

Lemma substitute_type_open : forall T k U theta,
  (forall X, locally_closed_ty (theta X)) -> locally_closed_ty U ->
  substitute_type_vars theta (open_ty_rec k U T) =
  open_ty_rec k (substitute_type_vars theta U) (substitute_type_vars theta T).
Proof.
  induction T; intros k U theta Htheta HU; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite (open_ty_rec_lc_noop (theta a) k
      (substitute_type_vars theta U)).
    + reflexivity.
    + apply lc_ty_weaken_to. apply Htheta.
  - rewrite IHT1, IHT2; try assumption. reflexivity.
  - rewrite IHT with (k := S k); try assumption. reflexivity.
Qed.

Lemma substitute_tm_type_open : forall t k U theta,
  (forall X, locally_closed_ty (theta X)) -> locally_closed_ty U ->
  substitute_tm_type_vars theta (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (substitute_type_vars theta U)
    (substitute_tm_type_vars theta t).
Proof.
  induction t; intros k U theta Htheta HU; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite substitute_type_open; try assumption.
    rewrite IHt; try assumption. reflexivity.
  - rewrite IHt1, IHt2; try assumption. reflexivity.
  - rewrite IHt with (k := S k); try assumption. reflexivity.
  - rewrite IHt, substitute_type_open; try assumption. reflexivity.
Qed.

Lemma substitute_tm_type_open_term : forall t k u theta,
  substitute_tm_type_vars theta (open_tm_rec k u t) =
  open_tm_rec k (substitute_tm_type_vars theta u)
    (substitute_tm_type_vars theta t).
Proof.
  induction t; intros k u theta; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - rewrite IHt1, IHt2. reflexivity.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
Qed.

Lemma tm_fvars_substitute_tm_type_vars : forall t theta,
  tm_fvars (substitute_tm_type_vars theta t) = tm_fvars t.
Proof.
  induction t; intros theta; simpl.
  - reflexivity.
  - reflexivity.
  - apply IHt.
  - rewrite IHt1, IHt2. reflexivity.
  - apply IHt.
  - apply IHt.
Qed.

Lemma substitute_ty_open_update : forall T theta X U,
  (forall Y, locally_closed_ty (theta Y)) -> locally_closed_ty U ->
  ~ In X (ty_fvars T) ->
  substitute_type_vars (update_type_subst theta X U)
    (open_ty T (Ty_FVar X)) =
  open_ty (substitute_type_vars theta T) U.
Proof.
  intros T theta X U Htheta HU Hfresh.
  unfold open_ty. rewrite substitute_type_open; try assumption.
  - unfold update_type_subst. destruct (Nat.eqb X X) eqn:E; [|apply Nat.eqb_neq in E; contradiction].
    cbn [substitute_type_vars]. rewrite E.
    fold (update_type_subst theta X U).
    rewrite substitute_type_update_absent by exact Hfresh.
    reflexivity.
  - intro Y. unfold update_type_subst. destruct (Nat.eqb Y X); auto.
  - constructor.
Qed.

Lemma substitute_tm_ty_open_update : forall t theta X U,
  (forall Y, locally_closed_ty (theta Y)) -> locally_closed_ty U ->
  ~ In X (tm_ty_fvars t) ->
  substitute_tm_type_vars (update_type_subst theta X U)
    (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (substitute_tm_type_vars theta t) U.
Proof.
  intros t theta X U Htheta HU Hfresh.
  unfold open_tm_ty. rewrite substitute_tm_type_open; try assumption.
  - unfold update_type_subst. destruct (Nat.eqb X X) eqn:E; [|apply Nat.eqb_neq in E; contradiction].
    cbn [substitute_type_vars]. rewrite E.
    fold (update_type_subst theta X U).
    rewrite substitute_tm_type_update_absent by exact Hfresh.
    reflexivity.
  - intro Y. unfold update_type_subst. destruct (Nat.eqb Y X); auto.
  - constructor.
Qed.

Lemma wf_ty_substitute : forall Delta T,
  wf_ty Delta T ->
  forall Delta' theta,
    (forall X, locally_closed_ty (theta X)) ->
    (forall X, In X Delta -> wf_ty Delta' (theta X)) ->
    wf_ty Delta' (substitute_type_vars theta T).
Proof.
  intros Delta T H.
  induction H as
    [Delta X Hin
    | Delta T1 T2 H1 IH1 H2 IH2
    | L Delta T Hbody IHbody]; intros Delta' theta Hlc Hwf.
  - simpl. apply Hwf. exact Hin.
  - simpl. apply WF_Arrow.
    + eapply IH1; eassumption.
    + eapply IH2; eassumption.
  - simpl. eapply WF_All with (L := L ++ Delta ++ ty_fvars T).
    intros Y HY.
    assert (HYL : ~ In Y L).
    { intro Hin. apply HY. apply in_or_app; left; exact Hin. }
    assert (HYDelta : ~ In Y Delta).
    { intro Hin. apply HY. apply in_or_app; right. apply in_or_app; left; exact Hin. }
    assert (HYfv : ~ In Y (ty_fvars T)).
    { intro Hin. apply HY. apply in_or_app; right. apply in_or_app; right; exact Hin. }
    specialize (IHbody Y HYL).
    set (thetaY := update_type_subst theta Y (Ty_FVar Y)).
    assert (HlcY : forall Z, locally_closed_ty (thetaY Z)).
    { intro Z. unfold thetaY, update_type_subst.
      destruct (Nat.eqb Z Y); [constructor|apply Hlc]. }
    assert (HwfY : forall Z, In Z (Y :: Delta) ->
      wf_ty (Y :: Delta') (thetaY Z)).
    { intros Z HZ. simpl in HZ. destruct HZ as [<-|HZ].
      - unfold thetaY, update_type_subst.
        destruct (Nat.eqb Y Y) eqn:E.
        + apply WF_Var. simpl; auto.
        + apply Nat.eqb_neq in E; contradiction.
      - assert (Z <> Y) by (intro E; subst; contradiction).
        unfold thetaY, update_type_subst.
        destruct (Nat.eqb Z Y) eqn:E.
        + apply Nat.eqb_eq in E; contradiction.
        + apply wf_ty_mono with (Delta := Delta').
          * apply Hwf. exact HZ.
          * intros W HW. simpl. now right.
    }
    pose proof (IHbody (Y :: Delta') thetaY HlcY HwfY) as Hresult.
    unfold thetaY in Hresult.
    rewrite (substitute_ty_open_update T theta Y (Ty_FVar Y)
      Hlc (lc_ty_fvar 0 Y) HYfv) in Hresult.
    exact Hresult.
Qed.

Lemma open_tm_ty_rec_lc_noop : forall t K k U,
  lc_tm_at K k t -> open_tm_ty_rec K U t = t.
Proof.
  induction t; intros K k U Hlc; simpl.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. rewrite open_ty_rec_lc_noop by assumption.
    f_equal. eapply IHt; eassumption.
  - inversion Hlc; subst. f_equal; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion Hlc; subst. f_equal. eapply IHt; eassumption.
  - inversion Hlc; subst. f_equal.
    + eapply IHt; eassumption.
    + match goal with
      | Hty : lc_ty_at K ?A |- _ => exact (open_ty_rec_lc_noop A K U Hty)
      end.
Qed.

Lemma instantiate_open_tm_ty_rec : forall t K U sigma,
  (forall x, locally_closed_tm (sigma x)) ->
  instantiate_tm sigma (open_tm_ty_rec K U t) =
  open_tm_ty_rec K U (instantiate_tm sigma t).
Proof.
  induction t; intros K U sigma Hsigma; simpl.
  - reflexivity.
  - symmetry. eapply open_tm_ty_rec_lc_noop with (k:=0).
    apply lc_tm_weaken_type_to. apply Hsigma.
  - f_equal. apply IHt. exact Hsigma.
  - rewrite IHt1, IHt2; [reflexivity|exact Hsigma|exact Hsigma].
  - f_equal. apply (IHt (S K) U sigma Hsigma).
  - rewrite IHt; [reflexivity|exact Hsigma].
Qed.

Lemma instantiate_open_tm_ty : forall t U sigma,
  (forall x, locally_closed_tm (sigma x)) ->
  instantiate_tm sigma (open_tm_ty t U) =
  open_tm_ty (instantiate_tm sigma t) U.
Proof.
  intros t U sigma Hsigma. unfold open_tm_ty.
  apply instantiate_open_tm_ty_rec. exact Hsigma.
Qed.

Lemma substitute_type_vars_identity : forall T,
  substitute_type_vars (fun X => Ty_FVar X) T = T.
Proof. induction T; simpl; congruence. Qed.

Lemma fold_max_bound : forall (L : list atom) (X : atom),
  In X L -> X <= fold_right Nat.max 0 L.
Proof.
  induction L as [|Y L IH]; intros X Hin; simpl in *; [contradiction|].
  destruct Hin as [->|Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [eapply IH; eassumption|apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall (L : list atom), exists X, ~ In X L.
Proof.
  intro L. exists (S (fold_right Nat.max 0 L)).
  intro Hin. pose proof (fold_max_bound L _ Hin). lia.
Qed.

Lemma open_ty_rec_lc : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor.
    match goal with
    | Hbody : lc_ty_at (S k) _ |- _ => eapply IHT with (k := S k); exact Hbody
    end.
Qed.

Lemma wf_ty_locally_closed : forall Delta T,
  wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H.
  - constructor.
  - constructor; assumption.
  - destruct (fresh_atom L) as [X HX].
    specialize (H0 X HX).
    apply open_ty_rec_lc with (k := 0) (X := X) in H0.
    constructor. exact H0.
Qed.

Lemma wf_ty_open : forall Delta T U,
  wf_ty Delta (Ty_All T) -> wf_ty Delta U -> wf_ty Delta (open_ty T U).
Proof.
  intros Delta T U Hall HU.
  inversion Hall as [| |L Delta0 A Hbody]; subst.
  destruct (fresh_atom (L ++ Delta ++ ty_fvars T)) as [X HX].
  assert (HXL : ~ In X L).
  { intro H; apply HX; apply in_or_app; now left. }
  assert (HXDelta : ~ In X Delta).
  { intro H; apply HX. apply in_or_app; right. apply in_or_app; now left. }
  assert (HXfv : ~ In X (ty_fvars T)).
  { intro H; apply HX. apply in_or_app; right. apply in_or_app; now right. }
  specialize (Hbody X HXL).
  set (theta := fun Y => Ty_FVar Y).
  set (thetaX := update_type_subst theta X U).
  assert (Hlc : forall Y, locally_closed_ty (thetaX Y)).
  { intro Y. unfold thetaX, theta, update_type_subst.
    destruct (Nat.eqb Y X); [exact (wf_ty_locally_closed Delta U HU)|constructor]. }
  assert (Hwf : forall Y, In Y (X :: Delta) ->
    wf_ty Delta (thetaX Y)).
  { intros Y HY. simpl in HY. destruct HY as [<-|HY].
    - unfold thetaX, update_type_subst. destruct (Nat.eqb X X) eqn:E; [exact HU|].
      apply Nat.eqb_neq in E. contradiction.
    - assert (Y <> X) by (intro E; subst; contradiction).
      unfold thetaX, theta, update_type_subst.
      destruct (Nat.eqb Y X) eqn:E.
      + apply Nat.eqb_eq in E; contradiction.
      + apply WF_Var. exact HY.
  }
  pose proof (wf_ty_substitute (X :: Delta) (open_ty T (Ty_FVar X))
    Hbody Delta thetaX Hlc Hwf) as Hsub.
  unfold thetaX in Hsub.
  rewrite (substitute_ty_open_update T theta X U
    (fun Y => lc_ty_fvar 0 Y)
    (wf_ty_locally_closed _ U HU) HXfv) in Hsub.
  rewrite substitute_type_vars_identity in Hsub.
  exact Hsub.
Qed.

Lemma has_type_wf_ty : forall Delta Gamma t T,
  has_type Delta Gamma t T -> wf_ty Delta T.
Proof.
  intros Delta Gamma t T Htyping.
  induction Htyping as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma T1 t2 T2 Hwf Hprem IHprem
    |Delta Gamma t1 t2 T1 T2 Hfun IHfun Harg IHarg
    |L Delta Gamma t T Hprem IHprem
    |Delta Gamma t T U Hbody IHbody HwfU].
  - exact Hwf.
  - apply WF_Arrow.
    + exact Hwf.
    + destruct (fresh_atom L) as [x Hx].
      specialize (IHprem x Hx). exact IHprem.
  - inversion IHfun; subst. exact H3.
  - eapply WF_All with (L:=L). intros X HX.
    apply IHprem. exact HX.
  - eapply wf_ty_open; eassumption.
Qed.

Lemma open_tm_rec_lc_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. constructor. lia.
    + apply Nat.eqb_neq in E. inversion Hlc; subst. constructor. lia.
  - constructor.
  - inversion Hlc; subst. constructor; [assumption|].
    match goal with
    | Hbody : lc_tm_at K (S k) _ |- _ =>
        eapply IHt with (K := K) (k := S k); exact Hbody
    end.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
  - inversion Hlc; subst. constructor. eapply IHt; eassumption.
  - inversion Hlc; subst. constructor; [eapply IHt; eassumption|assumption].
Qed.

Lemma open_tm_ty_rec_lc_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X Hlc; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - inversion Hlc; subst. constructor; assumption.
  - inversion Hlc; subst. constructor.
    + match goal with
      | Hty : lc_ty_at K (open_ty_rec K (Ty_FVar X) _) |- _ =>
          eapply open_ty_rec_lc; exact Hty
      end.
    + match goal with
      | Hbody : lc_tm_at K (S k) _ |- _ => eapply IHt; exact Hbody
      end.
  - inversion Hlc; subst. constructor.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
  - inversion Hlc; subst. constructor. eapply IHt; eassumption.
  - inversion Hlc; subst. constructor.
    + eapply IHt; eassumption.
    + match goal with
      | Hty : lc_ty_at K (open_ty_rec K (Ty_FVar X) _) |- _ =>
          eapply open_ty_rec_lc; exact Hty
      end.
Qed.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; induction H; intros; eauto using multi.
Qed.

Lemma step_deterministic : forall t u v, t --> u -> t --> v -> u = v.
Proof.
  intros t u v H; revert v; induction H; intros z Hz; inversion Hz; subst;
    try reflexivity; try congruence;
    try solve [f_equal; eapply IHstep; eassumption];
    try solve [inversion H3]; try solve [inversion H];
    try (match goal with
         | Hval : value ?q, Hred : ?q --> _ |- _ => inversion Hval; subst; inversion Hred
         end).
Qed.

Lemma multi_app1 : forall t u a, t -->* u -> locally_closed_tm a ->
  tm_app t a -->* tm_app u a.
Proof.
  intros t u a H; induction H; intros Ha; eauto using multi.
  eapply multi_step; [eapply ST_App1; eauto|]. eauto.
Qed.

Lemma multi_app2 : forall v t u, value v -> t -->* u ->
  tm_app v t -->* tm_app v u.
Proof.
  intros v t u Hv H; induction H; eauto using multi.
  eapply multi_step; [eapply ST_App2; eauto|]. exact IHmulti.
Qed.

Lemma multi_tapp : forall t u U, t -->* u -> locally_closed_ty U ->
  tm_tapp t U -->* tm_tapp u U.
Proof.
  intros t u U H; induction H; intros HU; eauto using multi.
  eapply multi_step; [eapply ST_TApp; eauto|]. eauto.
Qed.

Lemma value_locally_closed : forall v, value v -> locally_closed_tm v.
Proof. intros v H; inversion H; assumption. Qed.

Lemma has_type_locally_closed : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Htyping.
  induction Htyping as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma T1 t2 T2 Hwf Hprem IHprem
    |Delta Gamma t1 t2 T1 T2 Hfun IHfun Harg IHarg
    |L Delta Gamma t T Hprem IHprem
    |Delta Gamma t T U Hbody IHbody HwfU].
  - constructor.
  - destruct (fresh_atom L) as [x Hx].
    specialize (IHprem x Hx).
    assert (Hopen : locally_closed_tm (open_tm t2 (tm_fvar x))).
    { exact IHprem. }
    apply lc_tm_abs.
    + eapply wf_ty_locally_closed; eassumption.
    + eapply open_tm_rec_lc_inv with (x:=x). exact Hopen.
  - constructor; assumption.
  - destruct (fresh_atom L) as [X HX].
    specialize (IHprem X HX).
    assert (Hopen : locally_closed_tm (open_tm_ty t (Ty_FVar X))).
    { exact IHprem. }
    apply lc_tm_tabs.
    eapply open_tm_ty_rec_lc_inv with (X:=X). exact Hopen.
  - constructor.
    + eapply IHbody.
    + eapply wf_ty_locally_closed; eassumption.
Qed.

Lemma singleton_identity_from_relation : forall t U v,
  term_rel [] (fun _ => fun _ _ => True)
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) t t ->
  wf_ty [] U -> locally_closed_ty U -> value v ->
  tm_app (tm_tapp t U) v -->* v.
Proof.
  intros t U v Hterm HU HUlcv Hv.
  destruct Hterm as [f [g [Htf [Htg [Hfv [Hgv Hrel]]]]]].
  simpl in Hrel.
  destruct (Hrel U U (fun a b => a = v /\ b = v) HU HU)
    as [h1 [h2 [Hfh1 [Hgh2 [Hh1 [Hh2 Hhr]]]]]].
  simpl in Hhr.
  destruct (Hhr v v Hv Hv (conj eq_refl eq_refl))
    as [q1 [q2 [Hq1 [Hq2 [Hqv1 [Hqv2 [E1 E2]]]]]]].
  subst q1 q2.
  eapply multi_trans.
  - eapply multi_trans.
    + eapply multi_app1.
      * eapply multi_tapp; [exact Htf|exact HUlcv].
      * exact (value_locally_closed _ Hv).
    + eapply multi_trans.
      * eapply multi_app1; [exact Hfh1|]. exact (value_locally_closed _ Hv).
      * exact Hq1.
  - apply multi_refl.
Qed.

Lemma fundamental_theorem : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho theta1 theta2 xi sigma1 sigma2,
    type_context_rel Delta theta1 theta2 xi ->
    (forall X, locally_closed_ty (theta1 X) /\ locally_closed_ty (theta2 X)) ->
    term_context_rel [] xi Gamma sigma1 sigma2 ->
    (forall x, locally_closed_tm (sigma1 x) /\ locally_closed_tm (sigma2 x)) ->
    term_rel rho xi T
      (instantiate_tm sigma1 (substitute_tm_type_vars theta1 t))
      (instantiate_tm sigma2 (substitute_tm_type_vars theta2 t)).
Proof.
  intros Delta Gamma t T Htyping.
  induction Htyping as
    [Delta Gamma x T Hlookup Hwf
    |L Delta Gamma T1 body T2 Hwf Hprem IHprem
    |Delta Gamma t1 t2 T1 T2 Hfun IHfun Harg IHarg
    |L Delta Gamma body T Hprem IHprem
    |Delta Gamma t A U Hbody IHbody HwfU].
  - intros rho theta1 theta2 xi sigma1 sigma2 Hty Htheta Hctx Hsig.
    specialize (Hctx x T Hlookup).
    destruct Hctx as [Hv1 [Hv2 Hrel]].
    exists (sigma1 x), (sigma2 x). split; [apply multi_refl|].
    split; [apply multi_refl|]. split; [exact Hv1|].
    split; [exact Hv2|].
    apply (proj1 (value_rel_env_irrelevant T 0
      (wf_ty_locally_closed _ _ Hwf) [] rho xi (sigma1 x) (sigma2 x)
      ltac:(intros i Hi; lia))).
    exact Hrel.
  - intros rho theta1 theta2 xi sigma1 sigma2 Hty Htheta Hctx Hsig.
    destruct (fresh_atom (L ++ context_vars Gamma ++ tm_fvars body))
      as [x Hx].
    assert (HxL : ~ In x L).
    { intro H; apply Hx; apply in_or_app; now left. }
    assert (HxG : ~ In x (context_vars Gamma)).
    { intro H; apply Hx; apply in_or_app; right; apply in_or_app; now left. }
    assert (Hxbody : ~ In x (tm_fvars body)).
    { intro H; apply Hx; apply in_or_app; right; apply in_or_app; now right. }
    assert (Hlc1 : locally_closed_tm
      (instantiate_tm sigma1 (substitute_tm_type_vars theta1 (tm_abs T1 body)))).
    { eapply instantiate_tm_lc; [|exact (fun z => proj1 (Hsig z))].
      eapply substitute_tm_type_vars_lc; [|apply Htheta].
      eapply has_type_locally_closed. exact
        (T_Abs L Delta Gamma T1 body T2 Hwf Hprem).
    }
    assert (Hlc2 : locally_closed_tm
      (instantiate_tm sigma2 (substitute_tm_type_vars theta2 (tm_abs T1 body)))).
    { eapply instantiate_tm_lc; [|exact (fun z => proj2 (Hsig z))].
      eapply substitute_tm_type_vars_lc; [|apply Htheta].
      eapply has_type_locally_closed. exact
        (T_Abs L Delta Gamma T1 body T2 Hwf Hprem).
    }
    exists (instantiate_tm sigma1 (substitute_tm_type_vars theta1 (tm_abs T1 body))),
           (instantiate_tm sigma2 (substitute_tm_type_vars theta2 (tm_abs T1 body))).
    split; [constructor|]. split; [constructor|]. split.
    + constructor. exact Hlc1.
    + split; [constructor; exact Hlc2|].
      simpl. intros a b Ha Hb Hab.
      assert (Hab0 : value_rel [] xi T1 a b).
      { apply (proj2 (value_rel_env_irrelevant T1 0
          (wf_ty_locally_closed _ _ Hwf) [] rho xi a b
          ltac:(intros i Hi; lia))). exact Hab. }
      assert (Hctx' : term_context_rel [] xi (update Gamma x T1)
        (update_tm_subst sigma1 x a) (update_tm_subst sigma2 x b)).
      { eapply term_context_rel_update.
        - exact HxG.
        - exact Hctx.
        - exact Ha.
        - exact Hb.
        - exact Hab0.
      }
      assert (Hsig' : forall y,
        locally_closed_tm (update_tm_subst sigma1 x a y) /\
        locally_closed_tm (update_tm_subst sigma2 x b y)).
      { intro y. unfold update_tm_subst. destruct (Nat.eqb y x) eqn:E.
        - apply Nat.eqb_eq in E. subst y.
          split; apply value_locally_closed; assumption.
        - exact (Hsig y). }
      destruct (IHprem x HxL rho theta1 theta2 xi
        (update_tm_subst sigma1 x a) (update_tm_subst sigma2 x b)
        Hty Htheta Hctx' Hsig') as [q1 [q2 [Hq1 [Hq2 [Hqv1 [Hqv2 Hqr]]]]]].
      assert (E1 : instantiate_tm (update_tm_subst sigma1 x a)
          (substitute_tm_type_vars theta1 (open_tm body (tm_fvar x))) =
        open_tm
          (instantiate_tm sigma1 (substitute_tm_type_vars theta1 body)) a).
      { unfold open_tm. rewrite substitute_tm_type_open_term.
        rewrite instantiate_open_tm_rec.
        - assert (Earg : instantiate_tm (update_tm_subst sigma1 x a)
              (substitute_tm_type_vars theta1 (tm_fvar x)) = a).
          { simpl. unfold update_tm_subst. rewrite Nat.eqb_refl. reflexivity. }
          rewrite Earg.
          rewrite instantiate_update_absent by (rewrite tm_fvars_substitute_tm_type_vars; exact Hxbody).
          reflexivity.
        - exact (fun y => proj1 (Hsig' y)).
      }
      assert (E2 : instantiate_tm (update_tm_subst sigma2 x b)
          (substitute_tm_type_vars theta2 (open_tm body (tm_fvar x))) =
        open_tm
          (instantiate_tm sigma2 (substitute_tm_type_vars theta2 body)) b).
      { unfold open_tm. rewrite substitute_tm_type_open_term.
        rewrite instantiate_open_tm_rec.
        - assert (Earg : instantiate_tm (update_tm_subst sigma2 x b)
              (substitute_tm_type_vars theta2 (tm_fvar x)) = b).
          { simpl. unfold update_tm_subst. rewrite Nat.eqb_refl. reflexivity. }
          rewrite Earg.
          rewrite instantiate_update_absent by (rewrite tm_fvars_substitute_tm_type_vars; exact Hxbody).
          reflexivity.
        - exact (fun y => proj2 (Hsig' y)).
      }
      exists q1, q2. split.
      * eapply multi_step.
        -- eapply ST_AppAbs; [exact Hlc1|]. exact Ha.
        -- rewrite <- E1. exact Hq1.
      * split.
        -- eapply multi_step.
           ++ eapply ST_AppAbs; [exact Hlc2|]. exact Hb.
           ++ rewrite <- E2. exact Hq2.
        -- split; [exact Hqv1|]. split; [exact Hqv2|exact Hqr].
  - intros rho theta1 theta2 xi sigma1 sigma2 Hty Htheta Hctx Hsig.
    destruct (IHfun rho theta1 theta2 xi sigma1 sigma2 Hty Htheta Hctx Hsig)
      as [f1 [f2 [Hf1 [Hf2 [Hfv1 [Hfv2 Hfr]]]]]].
    destruct (IHarg rho theta1 theta2 xi sigma1 sigma2 Hty Htheta Hctx Hsig)
      as [a1 [a2 [Ha1 [Ha2 [Hav1 [Hav2 Har]]]]]].
    pose proof Hfr as Happly.
    assert (Hlcarg1 : locally_closed_tm
      (instantiate_tm sigma1 (substitute_tm_type_vars theta1 t2))).
    { eapply instantiate_tm_lc; [|exact (fun z => proj1 (Hsig z))].
      eapply substitute_tm_type_vars_lc; [|apply Htheta].
      eapply has_type_locally_closed. exact Harg. }
    assert (Hlcarg2 : locally_closed_tm
      (instantiate_tm sigma2 (substitute_tm_type_vars theta2 t2))).
    { eapply instantiate_tm_lc; [|exact (fun z => proj2 (Hsig z))].
      eapply substitute_tm_type_vars_lc; [|apply Htheta].
      eapply has_type_locally_closed. exact Harg. }
    destruct (Happly a1 a2 Hav1 Hav2 Har) as [r1 [r2 [Hr1 [Hr2 [Hrv1 [Hrv2 Hrr]]]]]].
    exists r1,r2. split.
    + eapply multi_trans.
      * eapply multi_app1; [exact Hf1|exact Hlcarg1].
      * eapply multi_trans.
        -- eapply multi_app2; [exact Hfv1|exact Ha1].
        -- exact Hr1.
    + split.
      * eapply multi_trans.
        -- eapply multi_app1; [exact Hf2|exact Hlcarg2].
        -- eapply multi_trans.
           ++ eapply multi_app2; [exact Hfv2|exact Ha2].
           ++ exact Hr2.
      * split; [exact Hrv1|]. split; [exact Hrv2|exact Hrr].
  - intros rho theta1 theta2 xi sigma1 sigma2 Hty Htheta Hctx Hsig.
    destruct (fresh_atom
      (L ++ Delta ++ context_fvars Gamma ++ ty_fvars T ++ tm_ty_fvars body))
      as [X HX].
    assert (HXL : ~ In X L).
    { intro H; apply HX; apply in_or_app; now left. }
    assert (HXDelta : ~ In X Delta).
    { intro H; apply HX. apply in_or_app; right. apply in_or_app; now left. }
    assert (HXGamma : ~ In X (context_fvars Gamma)).
    { intro H; apply HX. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. left. exact H. }
    assert (HXtype : ~ In X (ty_fvars T)).
    { intro H; apply HX. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. apply in_or_app. left. exact H. }
    assert (HXbody : ~ In X (tm_ty_fvars body)).
    { intro H; apply HX. repeat rewrite in_app_iff. tauto. }
    assert (Hlc1 : locally_closed_tm
      (instantiate_tm sigma1 (substitute_tm_type_vars theta1 (tm_tabs body)))).
    { eapply instantiate_tm_lc; [|exact (fun z => proj1 (Hsig z))].
      eapply substitute_tm_type_vars_lc; [|apply Htheta].
      eapply has_type_locally_closed. exact
        (T_TAbs L Delta Gamma body T Hprem). }
    assert (Hlc2 : locally_closed_tm
      (instantiate_tm sigma2 (substitute_tm_type_vars theta2 (tm_tabs body)))).
    { eapply instantiate_tm_lc; [|exact (fun z => proj2 (Hsig z))].
      eapply substitute_tm_type_vars_lc; [|apply Htheta].
      eapply has_type_locally_closed. exact
        (T_TAbs L Delta Gamma body T Hprem). }
    exists (instantiate_tm sigma1 (substitute_tm_type_vars theta1 (tm_tabs body))),
      (instantiate_tm sigma2 (substitute_tm_type_vars theta2 (tm_tabs body))).
    split; [constructor|]. split; [constructor|]. split.
    + constructor; exact Hlc1.
    + split; [constructor; exact Hlc2|].
      simpl. intros U1 V1 Q HU1 HV1.
      assert (Hctx' : term_context_rel [] (update_rel xi X Q)
        Gamma sigma1 sigma2).
      { eapply term_context_rel_update_relation; eauto. }
      assert (Hty1 : type_context_rel (X :: Delta)
        (update_type_subst theta1 X U1) (update_type_subst theta2 X V1)
        (update_rel xi X Q)).
      { eapply type_context_rel_update; eauto. }
      assert (Htheta' : forall Y,
        locally_closed_ty (update_type_subst theta1 X U1 Y) /\
        locally_closed_ty (update_type_subst theta2 X V1 Y)).
      { intro Y. unfold update_type_subst. destruct (Nat.eqb Y X); [split; eapply wf_ty_locally_closed; eassumption|apply Htheta]. }
      assert (Hbodyterm := IHprem X HXL (Q :: rho)
        (update_type_subst theta1 X U1) (update_type_subst theta2 X V1)
        (update_rel xi X Q) sigma1 sigma2 Hty1 Htheta' Hctx' Hsig).
      destruct Hbodyterm as [r1 [r2 [R1 [R2 [Rv1 [Rv2 Rrel]]]]]].
      assert (E1 : instantiate_tm sigma1
          (substitute_tm_type_vars (update_type_subst theta1 X U1)
            (open_tm_ty body (Ty_FVar X))) =
          instantiate_tm sigma1 (open_tm_ty
            (substitute_tm_type_vars theta1 body) U1)).
      { rewrite (substitute_tm_ty_open_update body theta1 X U1
          (fun Y => proj1 (Htheta Y))
          (wf_ty_locally_closed [] U1 HU1) HXbody). reflexivity. }
      assert (E2 : instantiate_tm sigma2
          (substitute_tm_type_vars (update_type_subst theta2 X V1)
            (open_tm_ty body (Ty_FVar X))) =
          instantiate_tm sigma2 (open_tm_ty
            (substitute_tm_type_vars theta2 body) V1)).
      { rewrite (substitute_tm_ty_open_update body theta2 X V1
          (fun Y => proj2 (Htheta Y))
          (wf_ty_locally_closed [] V1 HV1) HXbody). reflexivity. }
      exists r1, r2. split.
      * eapply multi_step.
        -- eapply ST_TAppTabs.
           ++ exact Hlc1.
           ++ eapply wf_ty_locally_closed; exact HU1.
        -- rewrite <- (instantiate_open_tm_ty (substitute_tm_type_vars theta1 body) U1 sigma1 (fun z => proj1 (Hsig z))). rewrite <- E1. exact R1.
      * split.
        -- eapply multi_step.
           ++ eapply ST_TAppTabs.
              ** exact Hlc2.
              ** eapply wf_ty_locally_closed; exact HV1.
           ++ rewrite <- (instantiate_open_tm_ty (substitute_tm_type_vars theta2 body) V1 sigma2 (fun z => proj2 (Hsig z))). rewrite <- E2. exact R2.
        -- split; [exact Rv1|]. split; [exact Rv2|].
           assert (HlcT : lc_ty_at 1 T).
           { pose proof (has_type_wf_ty _ _ _ _
                (T_TAbs L Delta Gamma body T Hprem)) as HwfAll.
             pose proof (wf_ty_locally_closed _ _ HwfAll) as HlcAll.
             inversion HlcAll; assumption. }
           apply (proj1 (value_rel_open_type T 0 HlcT rho xi X Q r1 r2
             HXtype ltac:(simpl; lia))).
           simpl. exact Rrel.
  - intros rho theta1 theta2 xi sigma1 sigma2 Hty Htheta Hctx Hsig.
    destruct (IHbody rho theta1 theta2 xi sigma1 sigma2 Hty Htheta Hctx Hsig)
      as [f1 [f2 [Hf1 [Hf2 [Hfv1 [Hfv2 Hfr]]]]]].
    pose proof (wf_ty_substitute Delta U HwfU [] theta1
      (fun X => proj1 (Htheta X))
      (fun X HX => proj1 (Hty X HX))) as Hwf1.
    pose proof (wf_ty_substitute Delta U HwfU [] theta2
      (fun X => proj2 (Htheta X))
      (fun X HX => proj2 (Hty X HX))) as Hwf2.
    set (U1 := substitute_type_vars theta1 U).
    set (U2 := substitute_type_vars theta2 U).
    assert (HU1 : wf_ty [] U1).
    { eapply wf_ty_mono; [exact Hwf1|]. intros Y HY; contradiction. }
    assert (HU2 : wf_ty [] U2).
    { eapply wf_ty_mono; [exact Hwf2|]. intros Y HY; contradiction. }
    set (RU := value_rel rho xi U).
    simpl in Hfr.
    destruct (Hfr U1 U2 RU HU1 HU2)
      as [r1 [r2 [Hr1 [Hr2 [Hrv1 [Hrv2 Hrel]]]]]].
    assert (HU1lc : locally_closed_ty U1) by (eapply wf_ty_locally_closed; eauto).
    assert (HU2lc : locally_closed_ty U2) by (eapply wf_ty_locally_closed; eauto).
    exists r1,r2. split.
    + eapply multi_trans.
      * eapply multi_tapp; [exact Hf1|exact HU1lc].
      * exact Hr1.
    + split.
      * eapply multi_trans.
        -- eapply multi_tapp; [exact Hf2|exact HU2lc].
        -- exact Hr2.
      * split; [exact Hrv1|]. split; [exact Hrv2|].
        assert (HlcA : lc_ty_at 1 A).
        { pose proof (has_type_wf_ty _ _ _ _ Hbody) as HwfAll.
          pose proof (wf_ty_locally_closed _ _ HwfAll) as HlcAll.
          inversion HlcAll; assumption. }
        apply (proj2 (value_rel_open_substitute A 0 HlcA rho xi U r1 r2
          (wf_ty_locally_closed _ _ HwfU) ltac:(simpl; lia))).
        exact Hrel.
Qed.



Lemma substitute_tm_type_vars_identity : forall t,
  substitute_tm_type_vars (fun X => Ty_FVar X) t = t.
Proof.
  induction t; simpl; try rewrite substitute_type_vars_identity;
    try rewrite IHt; try rewrite IHt1; try rewrite IHt2; reflexivity.
Qed.

Lemma instantiate_tm_identity : forall t,
  instantiate_tm (fun X => tm_fvar X) t = t.
Proof.
  induction t; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2;
    reflexivity.
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
  intros t Ht U v HU Hv Htyped.
  pose (theta := fun X : atom => Ty_FVar X).
  pose (sigma := fun X : atom => tm_fvar X).
  assert (Htheta : forall X, locally_closed_ty (theta X) /\
                            locally_closed_ty (theta X)).
  { intro X. split; constructor. }
  assert (Hctx : term_context_rel [] (fun _ => fun _ _ => True)
    empty sigma sigma).
  { intros x T Hlook. discriminate Hlook. }
  assert (Hsig : forall x, locally_closed_tm (sigma x) /\
                           locally_closed_tm (sigma x)).
  { intro x. split; constructor. }
  pose proof (fundamental_theorem [] empty t
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) Ht [] theta theta
    (fun _ => fun _ _ => True) sigma sigma
    (fun X HX => False_rect _ HX) Htheta Hctx Hsig) as Hfund.
  unfold theta, sigma in Hfund.
  rewrite substitute_tm_type_vars_identity, instantiate_tm_identity in Hfund.
  change (term_rel [] (fun _ => fun _ _ => True)
    (Ty_All (Ty_Arrow (Ty_BVar 0) (Ty_BVar 0))) t t) in Hfund.
  eapply singleton_identity_from_relation.
  - exact Hfund.
  - exact HU.
  - eapply wf_ty_locally_closed; eassumption.
  - exact Hv.
Qed.

End SystemFParametricityNoneHardTask.
