(** System F CBV strong-normalization benchmark, Hard variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationRecursionHardTask.

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
      has_type Delta Gamma (tm_natrec n b s) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* ===================================================================== *)
(* Auxiliary syntactic infrastructure                                    *)
(* ===================================================================== *)

Lemma not_in_app_l : forall (l1 l2 : list atom) x,
  ~ In x (l1 ++ l2) -> ~ In x l1.
Proof. intros l1 l2 x H Hx. apply H. apply in_or_app. auto. Qed.

Lemma not_in_app_r : forall (l1 l2 : list atom) x,
  ~ In x (l1 ++ l2) -> ~ In x l2.
Proof. intros l1 l2 x H Hx. apply H. apply in_or_app. auto. Qed.

Fixpoint max_atom_list (l : list atom) : atom :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (max_atom_list l')
  end.

Definition fresh_atom (l : list atom) : atom := S (max_atom_list l).

Lemma max_atom_list_ge : forall l x, In x l -> x <= max_atom_list l.
Proof.
  induction l as [| a l IH]; intros x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma fresh_atom_not_in : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l Hin. unfold fresh_atom in Hin.
  pose proof (max_atom_list_ge l (S (max_atom_list l)) Hin). lia.
Qed.

Fixpoint fvars_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fvars_ty T1 ++ fvars_ty T2
  | Ty_All T1 => fvars_ty T1
  | Ty_Nat => []
  end.

Fixpoint fvars_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ t1 => fvars_tm t1
  | tm_app t1 t2 => fvars_tm t1 ++ fvars_tm t2
  | tm_tabs t1 => fvars_tm t1
  | tm_tapp t1 _ => fvars_tm t1
  | tm_zero => []
  | tm_succ t1 => fvars_tm t1
  | tm_natrec n b s => fvars_tm n ++ fvars_tm b ++ fvars_tm s
  end.

Definition update_sigma (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then u else sigma y.

Fixpoint subst_all (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar y => sigma y
  | tm_abs T t1 => tm_abs T (subst_all sigma t1)
  | tm_app t1 t2 => tm_app (subst_all sigma t1) (subst_all sigma t2)
  | tm_tabs t1 => tm_tabs (subst_all sigma t1)
  | tm_tapp t1 T => tm_tapp (subst_all sigma t1) T
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (subst_all sigma t1)
  | tm_natrec n b s =>
      tm_natrec (subst_all sigma n) (subst_all sigma b) (subst_all sigma s)
  end.

Lemma subst_all_update_irrel : forall sigma x u t,
  ~ In x (fvars_tm t) ->
  subst_all (update_sigma sigma x u) t = subst_all sigma t.
Proof.
  intros sigma x u t. revert x u. induction t; intros x u Hnin; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hnin. simpl. auto.
    + unfold update_sigma. rewrite E. reflexivity.
  - f_equal. apply IHt. exact Hnin.
  - f_equal.
    + apply IHt1. apply not_in_app_l with (l2 := fvars_tm t2). exact Hnin.
    + apply IHt2. apply not_in_app_r with (l1 := fvars_tm t1). exact Hnin.
  - f_equal. apply IHt. exact Hnin.
  - f_equal. apply IHt. exact Hnin.
  - reflexivity.
  - f_equal. apply IHt. exact Hnin.
  - f_equal.
    + apply IHt1. intro Hin. apply Hnin.
      apply in_app_iff. left. exact Hin.
    + apply IHt2. intro Hin. apply Hnin.
      apply in_app_iff. right. apply in_app_iff. left. exact Hin.
    + apply IHt3. intro Hin. apply Hnin.
      apply in_app_iff. right. apply in_app_iff. right. exact Hin.
Qed.

(* ===================================================================== *)
(* Locally closed types                                                  *)
(* ===================================================================== *)

Lemma lc_ty_at_mono : forall k T, lc_ty_at k T -> forall k', k <= k' -> lc_ty_at k' T.
Proof.
  intros k T H.
  induction H as
    [ k0 i Hlt
    | k0 X
    | k0 T1 T2 H1 IH1 H2 IH2
    | k0 T0 H0 IH0
    | k0 ];
  intros k' Hle.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; [apply IH1; exact Hle | apply IH2; exact Hle].
  - apply lc_ty_all. apply IH0. lia.
  - apply lc_ty_nat.
Qed.

Lemma lc_ty_open_rec : forall k U T,
  lc_ty_at (S k) T -> lc_ty_at k U -> lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k U T. revert k U.
  induction T as [ n | X | T1 IHT1 T2 IHT2 | T0 IHT0 | ];
  intros k U Hlc HU; simpl.
  - (* BVar n *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact HU.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E.
      inversion Hlc; subst. lia.
  - (* FVar *) apply lc_ty_fvar.
  - (* Arrow *) inversion Hlc; subst. apply lc_ty_arrow.
    + apply IHT1 with (k := k); assumption.
    + apply IHT2 with (k := k); assumption.
  - (* All *) inversion Hlc; subst. apply lc_ty_all.
    apply IHT0 with (k := S k).
    + assumption.
    + apply lc_ty_at_mono with (k := k).
      * exact HU.
      * lia.
  - (* Nat *) apply lc_ty_nat.
Qed.

Lemma lc_ty_open_back : forall k T X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  intros k T. revert k.
  induction T as [ n | X0 | T1 IHT1 T2 IHT2 | T0 IHT0 | ];
  intros k X H; simpl in H.
  - (* BVar n *) destruct (Nat.eqb k n) eqn:E.
    + apply lc_ty_bvar. apply Nat.eqb_eq in E. subst. lia.
    + inversion H; subst. apply lc_ty_bvar. apply Nat.eqb_neq in E. lia.
  - (* FVar *) apply (lc_ty_fvar (S k) X0).
  - (* Arrow *) inversion H; subst. apply lc_ty_arrow; eauto.
  - (* All *) inversion H; subst. apply lc_ty_all.
    apply IHT0 with (k := S k) (X := X). assumption.
  - (* Nat *) apply lc_ty_nat.
Qed.

Lemma lc_ty_subst : forall X U T k,
  lc_ty_at k T -> lc_ty_at k U -> lc_ty_at k (ty_subst X U T).
Proof.
  intros X U T.
  induction T as [ n | a | T1 IHT1 T2 IHT2 | T0 IHT0 | ];
  intros k Hlc HU; simpl.
  - (* BVar *) apply lc_ty_bvar. inversion Hlc; subst. lia.
  - (* FVar *) destruct (Nat.eqb X a) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exact HU.
    + apply lc_ty_fvar.
  - (* Arrow *) inversion Hlc; subst. apply lc_ty_arrow.
    + apply IHT1 with (k := k); assumption.
    + apply IHT2 with (k := k); assumption.
  - (* All *) inversion Hlc; subst. apply lc_ty_all.
    apply IHT0 with (k := S k).
    + assumption.
    + apply lc_ty_at_mono with (k := k).
      * exact HU.
      * lia.
  - (* Nat *) apply lc_ty_nat.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H.
  induction H as
    [ Delta X Hin
    | Delta T1 T2 H1 IH1 H2 IH2
    | L Delta T0 Hprem IHprem
    | Delta ].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    pose proof (IHprem (fresh_atom L) (fresh_atom_not_in L)) as Hx.
    apply lc_ty_open_back with (k := 0) (T := T0) (X := fresh_atom L).
    simpl. exact Hx.
  - apply lc_ty_nat.
Qed.

Lemma has_type_lc_ty : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H.
  induction H as
    [ Delta Gamma x T Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U H1 IH1 HwfU
    | Delta Gamma
    | Delta Gamma n Hn IHn
    | Delta Gamma n b s T Hn IHn Hb IHb Hs IHs ].
  - apply wf_ty_lc with (Delta := Delta). exact Hwf.
  - apply lc_ty_arrow.
    + apply wf_ty_lc with (Delta := Delta). exact Hwf.
    + apply (IHbody (fresh_atom L) (fresh_atom_not_in L)).
  - inversion IH1; subst. assumption.
  - apply lc_ty_all.
    apply lc_ty_open_back with (k := 0) (X := fresh_atom L).
    apply (IHbody (fresh_atom L) (fresh_atom_not_in L)).
  - apply lc_ty_open_rec with (k := 0).
    + inversion IH1; subst. assumption.
    + apply wf_ty_lc with (Delta := Delta). exact HwfU.
  - apply lc_ty_nat.
  - assumption.
  - assumption.
Qed.

(* ===================================================================== *)
(* Locally closed terms                                                  *)
(* ===================================================================== *)

Lemma lc_tm_at_K_mono : forall K k t,
  lc_tm_at K k t -> forall K', K <= K' -> lc_tm_at K' k t.
Proof.
  intros K k t H.
  induction H as
    [ K0 k0 i Hlt
    | K0 k0 x
    | K0 k0 T t1 Hty Hbody IHbody
    | K0 k0 t1 t2 H1 IH1 H2 IH2
    | K0 k0 t1 Hbody IHbody
    | K0 k0 t1 T Ht IHt Hty
    | K0 k0
    | K0 k0 t1 Hbody IHbody
    | K0 k0 n b s Hn IHn Hb IHb Hs IHs ];
  intros K' Hle.
  - apply lc_tm_bvar. assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_at_mono with (k := K0); auto.
    + apply IHbody. assumption.
  - apply lc_tm_app.
    + apply IH1. assumption.
    + apply IH2. assumption.
  - apply lc_tm_tabs. apply IHbody. lia.
  - apply lc_tm_tapp.
    + apply IHt. assumption.
    + apply lc_ty_at_mono with (k := K0); auto.
  - apply lc_tm_zero.
  - apply lc_tm_succ. apply IHbody. assumption.
  - apply lc_tm_rec.
    + apply IHn. assumption.
    + apply IHb. assumption.
    + apply IHs. assumption.
Qed.

Lemma lc_tm_at_k_mono : forall K k t,
  lc_tm_at K k t -> forall k', k <= k' -> lc_tm_at K k' t.
Proof.
  intros K k t H.
  induction H as
    [ K0 k0 i Hlt
    | K0 k0 x
    | K0 k0 T t1 Hty Hbody IHbody
    | K0 k0 t1 t2 H1 IH1 H2 IH2
    | K0 k0 t1 Hbody IHbody
    | K0 k0 t1 T Ht IHt Hty
    | K0 k0
    | K0 k0 t1 Hbody IHbody
    | K0 k0 n b s Hn IHn Hb IHb Hs IHs ];
  intros k' Hle.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + assumption.
    + apply IHbody. lia.
  - apply lc_tm_app.
    + apply IH1. assumption.
    + apply IH2. assumption.
  - apply lc_tm_tabs. apply IHbody. assumption.
  - apply lc_tm_tapp.
    + apply IHt. assumption.
    + assumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ. apply IHbody. assumption.
  - apply lc_tm_rec.
    + apply IHn. assumption.
    + apply IHb. assumption.
    + apply IHs. assumption.
Qed.

Lemma lc_tm_open_rec : forall K k t v,
  lc_tm_at K (S k) t -> lc_tm_at K k v ->
  lc_tm_at K k (open_tm_rec k v t).
Proof.
  intros K k t. revert K k.
  induction t as
    [ n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
    | n IHn b IHb s IHs ];
  intros K k v Ht Hv; simpl.
  - (* bvar n *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact Hv.
    + apply lc_tm_bvar. apply Nat.eqb_neq in E.
      inversion Ht; subst. lia.
  - (* fvar *) apply lc_tm_fvar.
  - (* abs *) inversion Ht; subst. apply lc_tm_abs.
    + assumption.
    + apply IH1 with (k := S k) (v := v).
      * assumption.
      * apply lc_tm_at_k_mono with (k := k); auto.
  - (* app *) inversion Ht; subst. apply lc_tm_app.
    + apply IH1 with (k := k) (v := v); auto.
    + apply IH2 with (k := k) (v := v); auto.
  - (* tabs *) inversion Ht; subst. apply lc_tm_tabs.
    apply IH1 with (K := S K) (k := k) (v := v).
    + assumption.
    + apply lc_tm_at_K_mono with (K := K); auto.
  - (* tapp *) inversion Ht; subst. apply lc_tm_tapp.
    + apply IH1 with (k := k) (v := v); auto.
    + assumption.
  - (* zero *) apply lc_tm_zero.
  - (* succ *) inversion Ht; subst. apply lc_tm_succ.
    apply IH1 with (k := k) (v := v); auto.
  - (* natrec *) inversion Ht; subst. apply lc_tm_rec.
    + apply IHn with (k := k) (v := v); auto.
    + apply IHb with (k := k) (v := v); auto.
    + apply IHs with (k := k) (v := v); auto.
Qed.

Lemma lc_tm_open_back : forall K k t x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  intros K k t. revert K k.
  induction t as
    [ n | x0 | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
    | n IHn b IHb s IHs ];
  intros K k x H; simpl in H.
  - (* bvar n *) destruct (Nat.eqb k n) eqn:E.
    + apply lc_tm_bvar. apply Nat.eqb_eq in E. subst. lia.
    + inversion H; subst. apply lc_tm_bvar. apply Nat.eqb_neq in E. lia.
  - (* fvar *) apply lc_tm_fvar.
  - (* abs *) inversion H; subst. apply lc_tm_abs.
    + assumption.
    + apply IH1 with (k := S k) (x := x). assumption.
  - (* app *) inversion H; subst. apply lc_tm_app.
    + apply IH1 with (k := k) (x := x). assumption.
    + apply IH2 with (k := k) (x := x). assumption.
  - (* tabs *) inversion H; subst. apply lc_tm_tabs.
    apply IH1 with (K := S K) (k := k) (x := x). assumption.
  - (* tapp *) inversion H; subst. apply lc_tm_tapp.
    + apply IH1 with (k := k) (x := x). assumption.
    + assumption.
  - (* zero *) apply lc_tm_zero.
  - (* succ *) inversion H; subst. apply lc_tm_succ.
    apply IH1 with (k := k) (x := x). assumption.
  - (* natrec *) inversion H; subst. apply lc_tm_rec.
    + apply IHn with (k := k) (x := x). assumption.
    + apply IHb with (k := k) (x := x). assumption.
    + apply IHs with (k := k) (x := x). assumption.
Qed.

Lemma lc_tm_ty_open : forall K k t U,
  lc_tm_at (S K) k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t. revert K k.
  induction t as
    [ n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
    | n IHn b IHb s IHs ];
  intros K k U Ht HU; simpl.
  - (* bvar *) apply lc_tm_bvar. inversion Ht; subst. lia.
  - (* fvar *) apply lc_tm_fvar.
  - (* abs *) inversion Ht; subst. apply lc_tm_abs.
    + apply lc_ty_open_rec with (k := K) (U := U); assumption.
    + apply IH1 with (K := K) (k := S k); assumption.
  - (* app *) inversion Ht; subst. apply lc_tm_app.
    + apply IH1 with (K := K) (k := k); assumption.
    + apply IH2 with (K := K) (k := k); assumption.
  - (* tabs *) inversion Ht; subst. apply lc_tm_tabs.
    apply IH1 with (K := S K) (k := k).
    + assumption.
    + apply lc_ty_at_mono with (k := K); auto.
  - (* tapp *) inversion Ht; subst. apply lc_tm_tapp.
    + apply IH1 with (K := K) (k := k); assumption.
    + apply lc_ty_open_rec with (k := K) (U := U); assumption.
  - (* zero *) apply lc_tm_zero.
  - (* succ *) inversion Ht; subst. apply lc_tm_succ.
    apply IH1 with (K := K) (k := k); assumption.
  - (* natrec *) inversion Ht; subst. apply lc_tm_rec.
    + apply IHn with (K := K) (k := k); assumption.
    + apply IHb with (K := K) (k := k); assumption.
    + apply IHs with (K := K) (k := k); assumption.
Qed.

Lemma lc_tm_ty_open_back : forall K k t X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  intros K k t. revert K k.
  induction t as
    [ n | x0 | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
    | n IHn b IHb s IHs ];
  intros K k X H; simpl in H.
  - (* bvar *) inversion H; subst. apply lc_tm_bvar. assumption.
  - (* fvar *) apply lc_tm_fvar.
  - (* abs *) inversion H; subst. apply lc_tm_abs.
    + apply lc_ty_open_back with (k := K) (X := X). assumption.
    + apply IH1 with (k := S k) (X := X). assumption.
  - (* app *) inversion H; subst. apply lc_tm_app.
    + apply IH1 with (k := k) (X := X). assumption.
    + apply IH2 with (k := k) (X := X). assumption.
  - (* tabs *) inversion H; subst. apply lc_tm_tabs.
    apply IH1 with (K := S K) (k := k) (X := X). assumption.
  - (* tapp *) inversion H; subst. apply lc_tm_tapp.
    + apply IH1 with (k := k) (X := X). assumption.
    + apply lc_ty_open_back with (k := K) (X := X). assumption.
  - (* zero *) apply lc_tm_zero.
  - (* succ *) inversion H; subst. apply lc_tm_succ.
    apply IH1 with (k := k) (X := X). assumption.
  - (* natrec *) inversion H; subst. apply lc_tm_rec.
    + apply IHn with (k := k) (X := X). assumption.
    + apply IHb with (k := k) (X := X). assumption.
    + apply IHs with (k := k) (X := X). assumption.
Qed.

Lemma lc_tm_ty_subst : forall K k t X U,
  lc_tm_at K k t -> lc_ty_at K U ->
  lc_tm_at K k (tm_ty_subst X U t).
Proof.
  intros K k t. revert K k.
  induction t as
    [ n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
    | n IHn b IHb s IHs ];
  intros K k X U Ht HU; simpl.
  - (* bvar *) apply lc_tm_bvar. inversion Ht; subst. lia.
  - (* fvar *) apply lc_tm_fvar.
  - (* abs *) inversion Ht; subst. apply lc_tm_abs.
    + apply lc_ty_subst; assumption.
    + apply IH1 with (K := K) (k := S k); assumption.
  - (* app *) inversion Ht; subst. apply lc_tm_app.
    + apply IH1 with (K := K) (k := k); assumption.
    + apply IH2 with (K := K) (k := k); assumption.
  - (* tabs *) inversion Ht; subst. apply lc_tm_tabs.
    apply IH1 with (K := S K) (k := k).
    + assumption.
    + apply lc_ty_at_mono with (k := K); auto.
  - (* tapp *) inversion Ht; subst. apply lc_tm_tapp.
    + apply IH1 with (K := K) (k := k); assumption.
    + apply lc_ty_subst; assumption.
  - (* zero *) apply lc_tm_zero.
  - (* succ *) inversion Ht; subst. apply lc_tm_succ.
    apply IH1 with (K := K) (k := k); assumption.
  - (* natrec *) inversion Ht; subst. apply lc_tm_rec.
    + apply IHn with (K := K) (k := k); assumption.
    + apply IHb with (K := K) (k := k); assumption.
    + apply IHs with (K := K) (k := k); assumption.
Qed.

Lemma open_ty_rec_lc_id : forall T K U k,
  lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  intros T. induction T as [ n | X | T1 IH1 T2 IH2 | T0 IH0 | ];
  intros K U k Hlc Hle; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. inversion Hlc; subst. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + apply IH1 with (K := K) (k := k); assumption.
    + apply IH2 with (K := K) (k := k); assumption.
  - inversion Hlc; subst. f_equal.
    apply IH0 with (K := S K) (k := S k); [assumption | lia].
  - reflexivity.
Qed.

Lemma open_tm_rec_lc_id : forall t K kb k v,
  kb <= k -> lc_tm_at K kb t -> open_tm_rec k v t = t.
Proof.
  intros t. induction t as
    [ n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
    | n IHn b IHb s IHs ];
  intros K kb k v Hle Hlc; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. inversion Hlc; subst. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst.
    erewrite (IH1 K (S kb) (S k) v); [reflexivity | lia | eassumption].
  - inversion Hlc; subst.
    erewrite (IH1 K kb k v); [| exact Hle | eassumption].
    erewrite (IH2 K kb k v); [reflexivity | exact Hle | eassumption].
  - inversion Hlc; subst.
    erewrite (IH1 (S K) kb k v); [reflexivity | exact Hle | eassumption].
  - inversion Hlc; subst.
    erewrite (IH1 K kb k v); [reflexivity | exact Hle | eassumption].
  - reflexivity.
  - inversion Hlc; subst.
    erewrite (IH1 K kb k v); [reflexivity | exact Hle | eassumption].
  - inversion Hlc; subst.
    erewrite (IHn K kb k v); [| exact Hle | eassumption].
    erewrite (IHb K kb k v); [| exact Hle | eassumption].
    erewrite (IHs K kb k v); [reflexivity | exact Hle | eassumption].
Qed.

Lemma open_tm_ty_rec_lc_id : forall t K kb k U,
  K <= k -> lc_tm_at K kb t -> open_tm_ty_rec k U t = t.
Proof.
  intros t. induction t as
    [ n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
    | n IHn b IHb s IHs ];
  intros K kb k U Hle Hlc; simpl.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + apply open_ty_rec_lc_id with (K := K) (k := k); assumption.
    + erewrite (IH1 K (S kb) k U); [reflexivity | exact Hle | eassumption].
  - inversion Hlc; subst. f_equal.
    + erewrite (IH1 K kb k U); [reflexivity | exact Hle | eassumption].
    + erewrite (IH2 K kb k U); [reflexivity | exact Hle | eassumption].
  - inversion Hlc; subst.
    erewrite (IH1 (S K) kb (S k) U); [reflexivity | lia | eassumption].
  - inversion Hlc; subst. f_equal.
    + erewrite (IH1 K kb k U); [reflexivity | exact Hle | eassumption].
    + apply open_ty_rec_lc_id with (K := K) (k := k); assumption.
  - reflexivity.
  - inversion Hlc; subst.
    erewrite (IH1 K kb k U); [reflexivity | exact Hle | eassumption].
  - inversion Hlc; subst. f_equal.
    + erewrite (IHn K kb k U); [reflexivity | exact Hle | eassumption].
    + erewrite (IHb K kb k U); [reflexivity | exact Hle | eassumption].
    + erewrite (IHs K kb k U); [reflexivity | exact Hle | eassumption].
Qed.

Lemma subst_all_open_tm_fvar_rec : forall sigma x u t,
  (forall y, locally_closed_tm (sigma y)) ->
  ~ In x (fvars_tm t) ->
  forall k,
  subst_all (update_sigma sigma x u) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k u (subst_all sigma t).
Proof.
  intros sigma x u t. revert sigma x u.
  induction t as
    [ n | a | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
    | n IHn b IHb s IHs ];
  intros sigma x u Hsig Hnin k; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. unfold update_sigma. simpl.
      rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - assert (Hax : a <> x).
    { intro. subst. apply Hnin. simpl. auto. }
    assert (Hupdate : update_sigma sigma x u a = sigma a).
    { unfold update_sigma. destruct (Nat.eqb a x) eqn:E.
      - apply Nat.eqb_eq in E. exfalso. apply Hax. exact E.
      - reflexivity. }
    rewrite Hupdate.
    rewrite (open_tm_rec_lc_id (sigma a) 0 0 k u).
    + reflexivity.
    + lia.
    + apply Hsig.
  - (* abs *) f_equal.
    apply IH1 with (x := x) (sigma := sigma) (u := u).
    + exact Hsig.
    + exact Hnin.
  - (* app *) f_equal.
    + apply IH1 with (x := x) (sigma := sigma) (u := u).
      * exact Hsig.
      * apply not_in_app_l with (l2 := fvars_tm t2). exact Hnin.
    + apply IH2 with (x := x) (sigma := sigma) (u := u).
      * exact Hsig.
      * apply not_in_app_r with (l1 := fvars_tm t1). exact Hnin.
  - (* tabs *) f_equal.
    apply IH1 with (x := x) (sigma := sigma) (u := u).
    + exact Hsig.
    + exact Hnin.
  - (* tapp *) f_equal.
    apply IH1 with (x := x) (sigma := sigma) (u := u).
    + exact Hsig.
    + exact Hnin.
  - (* zero *) reflexivity.
  - (* succ *) f_equal.
    apply IH1 with (x := x) (sigma := sigma) (u := u).
    + exact Hsig.
    + exact Hnin.
  - (* natrec *) f_equal.
    + apply IHn with (x := x) (sigma := sigma) (u := u).
      * exact Hsig.
      * apply not_in_app_l with (l2 := fvars_tm b ++ fvars_tm s). exact Hnin.
    + apply IHb with (x := x) (sigma := sigma) (u := u).
      * exact Hsig.
      * apply not_in_app_l with (l2 := fvars_tm s).
        apply not_in_app_r with (l1 := fvars_tm n). exact Hnin.
    + apply IHs with (x := x) (sigma := sigma) (u := u).
      * exact Hsig.
      * apply not_in_app_r with (l1 := fvars_tm b).
        apply not_in_app_r with (l1 := fvars_tm n). exact Hnin.
Qed.

Lemma subst_all_open_tm_ty_lc : forall sigma,
  (forall y, locally_closed_tm (sigma y)) ->
  forall k U t,
  subst_all sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (subst_all sigma t).
Proof.
  intros sigma Hsig k U t. revert k U.
  induction t as
    [ n | a | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
    | n IHn b IHb s IHs ];
  intros k U; simpl.
  - reflexivity.
  - rewrite (open_tm_ty_rec_lc_id (sigma a) 0 0 k U).
    + reflexivity.
    + lia.
    + apply Hsig.
  - f_equal. apply IH1.
  - f_equal.
    + apply IH1.
    + apply IH2.
  - f_equal. apply IH1.
  - f_equal. apply IH1.
  - reflexivity.
  - f_equal. apply IH1.
  - f_equal.
    + apply IHn.
    + apply IHb.
    + apply IHs.
Qed.

(* ===================================================================== *)
(* Type erasure: type annotations are computationally irrelevant         *)
(* ===================================================================== *)

Fixpoint erase_tm (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs _ t1 => tm_abs Ty_Nat (erase_tm t1)
  | tm_app t1 t2 => tm_app (erase_tm t1) (erase_tm t2)
  | tm_tabs t1 => tm_tabs (erase_tm t1)
  | tm_tapp t1 _ => tm_tapp (erase_tm t1) Ty_Nat
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (erase_tm t1)
  | tm_natrec n b s => tm_natrec (erase_tm n) (erase_tm b) (erase_tm s)
  end.

Lemma erase_tm_open_tm : forall k v t,
  erase_tm (open_tm_rec k v t) = open_tm_rec k (erase_tm v) (erase_tm t).
Proof.
  intros k v t. revert k v.
  induction t as
    [ n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
    | n IHn b IHb s IHs ];
  intros k v; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal. apply IH1.
  - f_equal; auto.
  - f_equal. apply IH1.
  - f_equal. apply IH1.
  - reflexivity.
  - f_equal. apply IH1.
  - f_equal; auto.
Qed.

Lemma erase_tm_open_tm_ty : forall k U t,
  erase_tm (open_tm_ty_rec k U t) = erase_tm t.
Proof.
  intros k U t. revert k U.
  induction t as
    [ n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
    | n IHn b IHb s IHs ];
  intros k U; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IH1.
  - f_equal; auto.
  - f_equal. apply IH1.
  - f_equal. apply IH1.
  - reflexivity.
  - f_equal. apply IH1.
  - f_equal; auto.
Qed.

Lemma erase_tm_ty_subst : forall X U t,
  erase_tm (tm_ty_subst X U t) = erase_tm t.
Proof.
  intros X U t. revert X U.
  induction t as
    [ n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
    | n IHn b IHb s IHs ];
  intros X U; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal. apply IH1.
  - f_equal; auto.
  - f_equal. apply IH1.
  - f_equal. apply IH1.
  - reflexivity.
  - f_equal. apply IH1.
  - f_equal; auto.
Qed.

Lemma erase_tm_bvar_inv : forall t i, erase_tm t = tm_bvar i -> t = tm_bvar i.
Proof.
  intros t i H. destruct t; simpl in H; try discriminate; inversion H; reflexivity.
Qed.

Lemma erase_tm_fvar_inv : forall t x, erase_tm t = tm_fvar x -> t = tm_fvar x.
Proof.
  intros t x H. destruct t; simpl in H; try discriminate; inversion H; reflexivity.
Qed.

Lemma erase_tm_zero_inv : forall t, erase_tm t = tm_zero -> t = tm_zero.
Proof.
  intros t H. destruct t; simpl in H; try discriminate; reflexivity.
Qed.

Lemma erase_tm_abs_inv : forall t b,
  erase_tm t = tm_abs Ty_Nat b ->
  exists T t1, t = tm_abs T t1 /\ erase_tm t1 = b.
Proof.
  intros t b H. destruct t; simpl in H; try discriminate.
  inversion H; subst. eauto.
Qed.

Lemma erase_tm_tabs_inv : forall t b,
  erase_tm t = tm_tabs b -> exists t1, t = tm_tabs t1 /\ erase_tm t1 = b.
Proof.
  intros t b H. destruct t; simpl in H; try discriminate.
  inversion H; subst. eauto.
Qed.

Lemma erase_tm_succ_inv : forall t b,
  erase_tm t = tm_succ b -> exists t1, t = tm_succ t1 /\ erase_tm t1 = b.
Proof.
  intros t b H. destruct t; simpl in H; try discriminate.
  inversion H; subst. eauto.
Qed.

Lemma erase_tm_app_inv : forall t a b,
  erase_tm t = tm_app a b ->
  exists t1 t2, t = tm_app t1 t2 /\ erase_tm t1 = a /\ erase_tm t2 = b.
Proof.
  intros t a b H. destruct t; simpl in H; try discriminate.
  inversion H; subst. eauto.
Qed.

Lemma erase_tm_tapp_inv : forall t b,
  erase_tm t = tm_tapp b Ty_Nat -> exists t1 T, t = tm_tapp t1 T /\ erase_tm t1 = b.
Proof.
  intros t b H. destruct t; simpl in H; try discriminate.
  inversion H; subst. eauto.
Qed.

Lemma erase_tm_natrec_inv : forall t n b s,
  erase_tm t = tm_natrec n b s ->
  exists n' b' s', t = tm_natrec n' b' s' /\
    erase_tm n' = n /\ erase_tm b' = b /\ erase_tm s' = s.
Proof.
  intros t n b s H.
  destruct t as [i | x | T t0 | t0 t3 | t0 | t0 T | | t0 | n0 b0 s0];
    simpl in H; try discriminate.
  inversion H; subst. exists n0, b0, s0. simpl. auto.
Qed.

(* ===================================================================== *)
(* Numeric values                                                        *)
(* ===================================================================== *)

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H. induction H as [| m Hm IHm].
  - apply lc_tm_zero.
  - apply lc_tm_succ. assumption.
Qed.

Lemma SN_succ : forall n, strongly_normalizing n -> strongly_normalizing (tm_succ n).
Proof.
  intros n H. induction H as [n Hstep IH].
  apply SN_intro. intros u Hu. inversion Hu; subst. apply IH. assumption.
Qed.

Lemma numeric_value_sn : forall n, numeric_value n -> strongly_normalizing n.
Proof.
  intros n H. induction H as [| m Hm IHm].
  - apply SN_intro. intros u Hu. inversion Hu.
  - apply SN_succ. assumption.
Qed.

Lemma numeric_value_no_step : forall n, numeric_value n -> forall n', ~ step n n'.
Proof.
  intros n H. induction H as [| m Hm IHm]; intros n' Hs.
  - inversion Hs.
  - inversion Hs; subst. eapply IHm. eassumption.
Qed.

Lemma numeric_value_bvar_absurd : forall i, ~ numeric_value (tm_bvar i).
Proof. intros i H. inversion H. Qed.

Lemma numeric_value_fvar_absurd : forall x, ~ numeric_value (tm_fvar x).
Proof. intros x H. inversion H. Qed.

Lemma numeric_value_abs_absurd : forall T t, ~ numeric_value (tm_abs T t).
Proof. intros T t H. inversion H. Qed.

Lemma numeric_value_app_absurd : forall a b, ~ numeric_value (tm_app a b).
Proof. intros a b H. inversion H. Qed.

Lemma numeric_value_tabs_absurd : forall t, ~ numeric_value (tm_tabs t).
Proof. intros t H. inversion H. Qed.

Lemma numeric_value_tapp_absurd : forall t T, ~ numeric_value (tm_tapp t T).
Proof. intros t T H. inversion H. Qed.

Lemma numeric_value_natrec_absurd : forall n b s, ~ numeric_value (tm_natrec n b s).
Proof. intros n b s H. inversion H. Qed.

Lemma value_app_absurd : forall a b, ~ value (tm_app a b).
Proof.
  intros a b Hv. inversion Hv.
  match goal with H : numeric_value (tm_app a b) |- _ =>
    exact (numeric_value_app_absurd a b H) end.
Qed.

Lemma value_fvar_absurd : forall x, ~ value (tm_fvar x).
Proof.
  intros x Hv. inversion Hv.
  match goal with H : numeric_value (tm_fvar x) |- _ =>
    exact (numeric_value_fvar_absurd x H) end.
Qed.

Lemma value_tapp_absurd : forall t T, ~ value (tm_tapp t T).
Proof.
  intros t T Hv. inversion Hv.
  match goal with H : numeric_value (tm_tapp t T) |- _ =>
    exact (numeric_value_tapp_absurd t T H) end.
Qed.

Lemma value_natrec_absurd : forall n b s, ~ value (tm_natrec n b s).
Proof.
  intros n b s Hv. inversion Hv.
  match goal with H : numeric_value (tm_natrec n b s) |- _ =>
    exact (numeric_value_natrec_absurd n b s H) end.
Qed.

Lemma numeric_erase : forall n, numeric_value n -> forall n',
  erase_tm n' = erase_tm n -> numeric_value n'.
Proof.
  intros n H. induction H as [| m Hm IHm]; intros n' He.
  - destruct n'; simpl in He; try discriminate. apply nv_zero.
  - destruct n'; simpl in He; try discriminate.
    inversion He; subst. apply nv_succ. apply IHm. assumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H. induction H.
  - assumption.
  - assumption.
  - apply numeric_value_lc. assumption.
Qed.

Lemma value_erase : forall v, value v -> forall v',
  erase_tm v' = erase_tm v -> locally_closed_tm v' -> value v'.
Proof.
  intros v Hv. induction Hv as [T t Hlc | t Hlc | n Hnv].
  - intros v' He Hlc'. destruct v'; simpl in He; try discriminate.
    inversion He; subst. apply v_abs. assumption.
  - intros v' He Hlc'. destruct v'; simpl in He; try discriminate.
    inversion He; subst. apply v_tabs. assumption.
  - intros v' He Hlc'. apply v_nat. apply (numeric_erase n Hnv v'). exact He.
Qed.

(* ===================================================================== *)
(* Step preserves local closure                                          *)
(* ===================================================================== *)

Lemma lc_tm_step : forall t t', step t t' ->
  locally_closed_tm t -> locally_closed_tm t'.
Proof.
  intros t t' Hstep.
  induction Hstep as
    [ T t v Hlcabs Hval
    | t1 t1' t2 Hsub IH Hlct2
    | v1 t2 t2' Hval Hsub IH
    | t T Hlctabs HlcT
    | t t' T Hsub IH HlcT
    | t t' Hsub IH
    | n n' b s Hsub IH Hlcb Hlcs
    | n b b' s Hnum Hsub IH Hlcs
    | n b s s' Hnum Hvalb Hsub IH
    | b s Hvalb Hvals
    | n b s Hnum Hvalb Hvals ];
  intros Hlc; inversion Hlc; subst.
  - (* AppAbs *) apply lc_tm_open_rec with (K := 0) (k := 0).
    + match goal with
      | H0 : lc_tm_at 0 0 (tm_abs _ _) |- _ => inversion H0; subst; assumption
      end.
    + assumption.
  - (* App1 *) apply lc_tm_app.
    + apply IH. assumption.
    + assumption.
  - (* App2 *) apply lc_tm_app.
    + assumption.
    + apply IH. assumption.
  - (* TAppTabs *) apply lc_tm_ty_open with (K := 0).
    + match goal with
      | H0 : lc_tm_at 0 0 (tm_tabs _) |- _ => inversion H0; subst; assumption
      end.
    + assumption.
  - (* TApp *) apply lc_tm_tapp.
    + apply IH. assumption.
    + assumption.
  - (* Succ *) apply lc_tm_succ. apply IH. assumption.
  - (* RecArg *) apply lc_tm_rec.
    + apply IH. assumption.
    + assumption.
    + assumption.
  - (* RecBase *) apply lc_tm_rec.
    + assumption.
    + apply IH. assumption.
    + assumption.
  - (* RecStep *) apply lc_tm_rec.
    + assumption.
    + assumption.
    + apply IH. assumption.
  - (* RecZero *) assumption.
  - (* RecSucc *) apply lc_tm_app.
    + apply lc_tm_app.
      * assumption.
      * match goal with
        | H0 : lc_tm_at 0 0 (tm_succ _) |- _ => inversion H0; subst; assumption
        end.
    + apply lc_tm_rec.
      * match goal with
        | H0 : lc_tm_at 0 0 (tm_succ _) |- _ => inversion H0; subst; assumption
        end.
      * assumption.
      * assumption.
Qed.

(* ===================================================================== *)
(* Simulation of reduction under type erasure                            *)
(* ===================================================================== *)

Lemma step_lift : forall t1 u1, step t1 u1 ->
  forall t2lift, erase_tm t2lift = erase_tm t1 -> locally_closed_tm t2lift ->
  exists u2, step t2lift u2 /\ erase_tm u2 = erase_tm u1 /\ locally_closed_tm u2.
Proof.
  intros t1 u1 Hstep.
  induction Hstep as
    [ T t v Hlcabs Hval
    | t1 t1' t2 Hsub IH Hlct2
    | v1 t2 t2' Hval Hsub IH
    | t T Hlctabs HlcT
    | t t' T Hsub IH HlcT
    | t t' Hsub IH
    | n n' b s Hsub IH Hlcb Hlcs
    | n b b' s Hnum Hsub IH Hlcs
    | n b s s' Hnum Hvalb Hsub IH
    | b s Hvalb Hvals
    | n b s Hnum Hvalb Hvals ];
  intros t2lift Herase Hlc; simpl in Herase.
  - (* ST_AppAbs *)
    destruct (erase_tm_app_inv t2lift _ _ Herase) as (a & b & E2 & Ea & Eb).
    subst t2lift.
    destruct (erase_tm_abs_inv a _ Ea) as (T' & body' & Ea' & Ebody).
    subst a.
    assert (Hlca : locally_closed_tm (tm_abs T' body'))
      by (inversion Hlc; subst; assumption).
    assert (Hlcb : locally_closed_tm b)
      by (inversion Hlc; subst; assumption).
    exists (open_tm body' b). split; [| split].
    + apply ST_AppAbs.
      * exact Hlca.
      * exact (value_erase v Hval b Eb Hlcb).
    + unfold open_tm. rewrite !erase_tm_open_tm. rewrite Ebody, Eb. reflexivity.
    + apply lc_tm_open_rec with (K := 0) (k := 0).
      * inversion Hlca; subst. assumption.
      * exact Hlcb.
  - (* ST_App1 *)
    destruct (erase_tm_app_inv t2lift _ _ Herase) as (a & b & E2 & Ea & Eb).
    subst t2lift.
    assert (Hlca : locally_closed_tm a) by (inversion Hlc; subst; assumption).
    assert (Hlcb : locally_closed_tm b) by (inversion Hlc; subst; assumption).
    destruct (IH a Ea Hlca) as (a' & Ha' & Ea' & Hlca').
    exists (tm_app a' b). split; [| split].
    + apply ST_App1; assumption.
    + simpl. rewrite Ea', Eb. reflexivity.
    + apply lc_tm_app; assumption.
  - (* ST_App2 *)
    destruct (erase_tm_app_inv t2lift _ _ Herase) as (a & b & E2 & Ea & Eb).
    subst t2lift.
    assert (Hlca : locally_closed_tm a) by (inversion Hlc; subst; assumption).
    assert (Hlcb : locally_closed_tm b) by (inversion Hlc; subst; assumption).
    destruct (IH b Eb Hlcb) as (b' & Hb' & Eb' & Hlcb').
    exists (tm_app a b'). split; [| split].
    + apply ST_App2.
      * exact (value_erase v1 Hval a Ea Hlca).
      * exact Hb'.
    + simpl. rewrite Ea, Eb'. reflexivity.
    + apply lc_tm_app; assumption.
  - (* ST_TAppTabs *)
    destruct (erase_tm_tapp_inv t2lift _ Herase) as (a & T' & E2 & Ea).
    subst t2lift.
    destruct (erase_tm_tabs_inv a _ Ea) as (body' & Ea' & Ebody).
    subst a.
    assert (Htabs' : locally_closed_tm (tm_tabs body'))
      by (inversion Hlc; subst; assumption).
    assert (HT' : lc_ty_at 0 T') by (inversion Hlc; subst; assumption).
    exists (open_tm_ty body' T'). split; [| split].
    + apply ST_TAppTabs; assumption.
    + unfold open_tm_ty. rewrite !erase_tm_open_tm_ty. rewrite Ebody. reflexivity.
    + apply lc_tm_ty_open with (K := 0).
      * inversion Htabs'; subst. assumption.
      * exact HT'.
  - (* ST_TApp *)
    destruct (erase_tm_tapp_inv t2lift _ Herase) as (a & T' & E2 & Ea).
    subst t2lift.
    assert (Hlca : locally_closed_tm a) by (inversion Hlc; subst; assumption).
    assert (HT' : lc_ty_at 0 T') by (inversion Hlc; subst; assumption).
    destruct (IH a Ea Hlca) as (a' & Ha' & Ea' & Hlca').
    exists (tm_tapp a' T'). split; [| split].
    + apply ST_TApp; assumption.
    + simpl. rewrite Ea'. reflexivity.
    + apply lc_tm_tapp; assumption.
  - (* ST_Succ *)
    destruct (erase_tm_succ_inv t2lift _ Herase) as (a & E2 & Ea).
    subst t2lift.
    assert (Hlca : locally_closed_tm a) by (inversion Hlc; subst; assumption).
    destruct (IH a Ea Hlca) as (a' & Ha' & Ea' & Hlca').
    exists (tm_succ a'). split; [| split].
    + apply ST_Succ. exact Ha'.
    + simpl. rewrite Ea'. reflexivity.
    + apply lc_tm_succ. assumption.
  - (* ST_RecArg *)
    destruct (erase_tm_natrec_inv t2lift _ _ _ Herase) as (a & b2 & c & E2 & Ea & Eb & Ec).
    subst t2lift.
    assert (Ha_lc : locally_closed_tm a) by (inversion Hlc; subst; assumption).
    assert (Hb_lc : locally_closed_tm b2) by (inversion Hlc; subst; assumption).
    assert (Hc_lc : locally_closed_tm c) by (inversion Hlc; subst; assumption).
    destruct (IH a Ea Ha_lc) as (a' & Ha' & Ea' & Hlca').
    exists (tm_natrec a' b2 c). split; [| split].
    + apply ST_RecArg; assumption.
    + simpl. rewrite Ea', Eb, Ec. reflexivity.
    + apply lc_tm_rec; assumption.
  - (* ST_RecBase *)
    destruct (erase_tm_natrec_inv t2lift _ _ _ Herase) as (a & b2 & c & E2 & Ea & Eb & Ec).
    subst t2lift.
    assert (Hlca : locally_closed_tm a) by (inversion Hlc; subst; assumption).
    assert (Hlcb : locally_closed_tm b2) by (inversion Hlc; subst; assumption).
    assert (Hlcc : locally_closed_tm c) by (inversion Hlc; subst; assumption).
    destruct (IH b2 Eb Hlcb) as (b2' & Hb' & Eb' & Hlcb').
    exists (tm_natrec a b2' c). split; [| split].
    + apply ST_RecBase.
      * apply (numeric_erase n Hnum); [exact Ea].
      * exact Hb'.
      * exact Hlcc.
    + simpl. rewrite Ea, Eb', Ec. reflexivity.
    + apply lc_tm_rec; assumption.
  - (* ST_RecStep *)
    destruct (erase_tm_natrec_inv t2lift _ _ _ Herase) as (a & b2 & c & E2 & Ea & Eb & Ec).
    subst t2lift.
    assert (Hlca : locally_closed_tm a) by (inversion Hlc; subst; assumption).
    assert (Hlcb : locally_closed_tm b2) by (inversion Hlc; subst; assumption).
    assert (Hlcc : locally_closed_tm c) by (inversion Hlc; subst; assumption).
    destruct (IH c Ec Hlcc) as (c' & Hc' & Ec' & Hlcc').
    exists (tm_natrec a b2 c'). split; [| split].
    + apply ST_RecStep.
      * exact (numeric_erase n Hnum a Ea).
      * exact (value_erase b Hvalb b2 Eb Hlcb).
      * exact Hc'.
    + simpl. rewrite Ea, Eb, Ec'. reflexivity.
    + apply lc_tm_rec; assumption.
  - (* ST_RecZero *)
    destruct (erase_tm_natrec_inv t2lift _ _ _ Herase) as (a & b2 & c & E2 & Ea & Eb & Ec).
    subst t2lift.
    assert (Hlca : a = tm_zero) by (apply erase_tm_zero_inv; exact Ea).
    subst a.
    assert (Hlcb : locally_closed_tm b2) by (inversion Hlc; subst; assumption).
    assert (Hcc : locally_closed_tm c) by (inversion Hlc; subst; assumption).
    exists b2. split; [| split].
    + apply ST_RecZero.
      * exact (value_erase b Hvalb b2 Eb Hlcb).
      * exact (value_erase s Hvals c Ec Hcc).
    + exact Eb.
    + exact Hlcb.
  - (* ST_RecSucc *)
    destruct (erase_tm_natrec_inv t2lift _ _ _ Herase) as (a & b2 & c & E2 & Ea & Eb & Ec).
    subst t2lift.
    destruct (erase_tm_succ_inv a _ Ea) as (n' & Ea' & En').
    subst a.
    assert (Hlcsn : locally_closed_tm (tm_succ n')) by (inversion Hlc; subst; assumption).
    assert (Hlcb : locally_closed_tm b2) by (inversion Hlc; subst; assumption).
    assert (Hlcc : locally_closed_tm c) by (inversion Hlc; subst; assumption).
    assert (Hlcn' : locally_closed_tm n') by (inversion Hlcsn; subst; assumption).
    exists (tm_app (tm_app c n') (tm_natrec n' b2 c)). split; [| split].
    + apply ST_RecSucc.
      * exact (numeric_erase n Hnum n' En').
      * exact (value_erase b Hvalb b2 Eb Hlcb).
      * exact (value_erase s Hvals c Ec Hlcc).
    + simpl. rewrite En', Eb, Ec. reflexivity.
    + apply lc_tm_app.
      * apply lc_tm_app; assumption.
      * apply lc_tm_rec; assumption.
Qed.

(* ===================================================================== *)
(* Erasure preserves strong normalization                                *)
(* ===================================================================== *)

Lemma erase_sn_fwd : forall t1, strongly_normalizing t1 ->
  locally_closed_tm t1 ->
  forall t2, erase_tm t2 = erase_tm t1 -> locally_closed_tm t2 ->
  strongly_normalizing t2.
Proof.
  intros t1 Hsn. induction Hsn as [t1 Hstep IH].
  intros Hlc1 t2 He Hlc2.
  apply SN_intro. intros u2 Hu2.
  destruct (step_lift t2 u2 Hu2 t1 (eq_sym He) Hlc1) as (u1 & Hu1 & He1 & Hlu1).
  apply (IH u1 Hu1 Hlu1 u2 (eq_sym He1) (lc_tm_step t2 u2 Hu2 Hlc2)).
Qed.

Lemma erase_sn : forall t1 t2,
  erase_tm t1 = erase_tm t2 ->
  locally_closed_tm t1 -> locally_closed_tm t2 ->
  (strongly_normalizing t1 <-> strongly_normalizing t2).
Proof.
  intros t1 t2 He Hlc1 Hlc2. split.
  - intros Hsn1. apply (erase_sn_fwd t1 Hsn1 Hlc1 t2 (eq_sym He) Hlc2).
  - intros Hsn2. apply (erase_sn_fwd t2 Hsn2 Hlc2 t1 He Hlc1).
Qed.

(* ===================================================================== *)
(* Reducibility candidates and the type-indexed logical relation         *)
(* ===================================================================== *)

Definition cand := tm -> Prop.

Definition cons_env (P : cand) (env : nat -> cand) : nat -> cand :=
  fun i => match i with 0 => P | S j => env j end.

Definition set_env (k : nat) (P : cand) (env : nat -> cand) : nat -> cand :=
  fun i => if Nat.eqb i k then P else env i.

Definition update_rho (rho : atom -> cand) (X : atom) (P : cand) : atom -> cand :=
  fun Y => if Nat.eqb Y X then P else rho Y.

Definition IsCand (P : cand) : Prop :=
  (forall t, P t -> locally_closed_tm t) /\
  (forall t, P t -> strongly_normalizing t) /\
  (forall t t', P t -> step t t' -> P t') /\
  (forall t, ~ value t -> locally_closed_tm t -> strongly_normalizing t ->
             (forall t', step t t' -> P t') -> P t) /\
  (forall t t', erase_tm t = erase_tm t' ->
                locally_closed_tm t -> locally_closed_tm t' -> (P t <-> P t')).

Fixpoint R (rho : atom -> cand) (env : nat -> cand) (T : ty) : cand :=
  match T with
  | Ty_BVar i => env i
  | Ty_FVar X => rho X
  | Ty_Nat => fun t => locally_closed_tm t /\ strongly_normalizing t
  | Ty_Arrow T1 T2 =>
      fun t => locally_closed_tm t /\ strongly_normalizing t /\
               (forall u, R rho env T1 u -> R rho env T2 (tm_app t u))
  | Ty_All T0 =>
      fun t => locally_closed_tm t /\ strongly_normalizing t /\
               (forall (P : cand) (U : ty), IsCand P -> locally_closed_ty U ->
                  R rho (cons_env P env) T0 (tm_tapp t U))
  end.

Lemma SN_step : forall t t', strongly_normalizing t -> step t t' -> strongly_normalizing t'.
Proof.
  intros t t' Hsn Hstep. inversion Hsn as [t0 Hred]. subst. eapply Hred. exact Hstep.
Qed.

Lemma SN_abs : forall T t, strongly_normalizing (tm_abs T t).
Proof.
  intros T t. apply SN_intro. intros u Hu. inversion Hu.
Qed.

Lemma SN_tabs : forall t, strongly_normalizing (tm_tabs t).
Proof.
  intros t. apply SN_intro. intros u Hu. inversion Hu.
Qed.

Lemma cons_env_set_env : forall (Q P : cand) env k i,
  cons_env Q (set_env k P env) i = set_env (S k) P (cons_env Q env) i.
Proof.
  intros Q P env k i. destruct i as [| j]; simpl.
  - destruct (Nat.eqb 0 (S k)) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - destruct (Nat.eqb j k); reflexivity.
Qed.

Lemma eqb_false_neq : forall x y : nat, (x =? y) = false -> x <> y.
Proof. intros x y E Heq. subst. rewrite Nat.eqb_refl in E. discriminate. Qed.

Lemma eqb_true_eq : forall x y : nat, (x =? y) = true -> x = y.
Proof. apply Nat.eqb_eq. Qed.

Lemma eqb_false_sym : forall x y : nat, (x =? y) = false -> (y =? x) = false.
Proof.
  intros x y H. apply Nat.eqb_neq. intro Heq.
  apply (eqb_false_neq x y H). symmetry. exact Heq.
Qed.

(* ===================================================================== *)
(* Basic candidate facts                                                 *)
(* ===================================================================== *)

Lemma lc_ty_at_bvar_inv : forall k i, lc_ty_at k (Ty_BVar i) -> i < k.
Proof. intros k i H. inversion H. assumption. Qed.

Lemma lc_ty_at_arrow_inv : forall k A B,
  lc_ty_at k (Ty_Arrow A B) -> lc_ty_at k A /\ lc_ty_at k B.
Proof. intros k A B H. inversion H; subst. split; assumption. Qed.

Lemma lc_ty_at_all_inv : forall k T, lc_ty_at k (Ty_All T) -> lc_ty_at (S k) T.
Proof. intros k T H. inversion H; subst. assumption. Qed.

Lemma lc_ty_at_nat_inv : forall k, lc_ty_at k Ty_Nat.
Proof. intros. apply lc_ty_nat. Qed.

Lemma R_env_agree : forall T rho env1 env2 k,
  lc_ty_at k T ->
  (forall i, i < k -> env1 i = env2 i) ->
  forall t, R rho env1 T t <-> R rho env2 T t.
Proof.
  intros T. induction T as [ i | X | A IHA B IHB | T0 IHT0 | ];
  intros rho env1 env2 k Hlc Hagree t; simpl in *.
  - (* BVar *) rewrite (Hagree i (lc_ty_at_bvar_inv k i Hlc)). reflexivity.
  - (* FVar *) reflexivity.
  - (* Arrow *)
    destruct (lc_ty_at_arrow_inv k A B Hlc) as [HlcA HlcB].
    split; intros [Hl [Hs H]].
    + split; [exact Hl | split; [exact Hs | intros u Hu]].
      apply (proj1 (IHB rho env1 env2 k HlcB Hagree (tm_app t u))).
      apply H. apply (proj2 (IHA rho env1 env2 k HlcA Hagree u)). exact Hu.
    + split; [exact Hl | split; [exact Hs | intros u Hu]].
      apply (proj2 (IHB rho env1 env2 k HlcB Hagree (tm_app t u))).
      apply H. apply (proj1 (IHA rho env1 env2 k HlcA Hagree u)). exact Hu.
  - (* All *)
    assert (HlcT0 : lc_ty_at (S k) T0) by (apply (lc_ty_at_all_inv k T0 Hlc)).
    split; intros [Hl [Hs H]].
    + split; [exact Hl | split; [exact Hs | intros P U HP HU]].
      assert (Hcons : forall i, i < S k -> cons_env P env1 i = cons_env P env2 i).
      { intros i Hi. destruct i as [| j]; simpl.
        - reflexivity.
        - apply Hagree. lia. }
      apply (proj1 (IHT0 rho (cons_env P env1) (cons_env P env2) (S k) HlcT0 Hcons (tm_tapp t U))).
      apply H; assumption.
    + split; [exact Hl | split; [exact Hs | intros P U HP HU]].
      assert (Hcons : forall i, i < S k -> cons_env P env1 i = cons_env P env2 i).
      { intros i Hi. destruct i as [| j]; simpl.
        - reflexivity.
        - apply Hagree. lia. }
      apply (proj2 (IHT0 rho (cons_env P env1) (cons_env P env2) (S k) HlcT0 Hcons (tm_tapp t U))).
      apply H; assumption.
  - (* Nat *) reflexivity.
Qed.

Lemma R_closed_env_irrel : forall T rho env1 env2 t,
  lc_ty_at 0 T -> (R rho env1 T t <-> R rho env2 T t).
Proof.
  intros T rho env1 env2 t Hlc.
  apply R_env_agree with (k := 0).
  - exact Hlc.
  - intros i Hi. lia.
Qed.

Lemma R_ty_open_rec : forall T rho env k U P,
  lc_ty_at (S k) T ->
  locally_closed_ty U ->
  (forall s, P s <-> R rho env U s) ->
  forall t,
  R rho (set_env k P env) T t <-> R rho env (open_ty_rec k U T) t.
Proof.
  intros T. induction T as [ i | X | A IHA B IHB | T0 IHT0 | ];
  intros rho env k U P Hlc HU HP t; simpl in *.
  - (* BVar i *) destruct (Nat.eqb k i) eqn:E.
    + apply eqb_true_eq in E. subst i.
      unfold set_env. simpl. rewrite Nat.eqb_refl. simpl. apply HP.
    + assert (Hik : (i =? k) = false) by (apply eqb_false_sym; exact E).
      unfold set_env. simpl. rewrite Hik. simpl. reflexivity.
  - (* FVar *) reflexivity.
  - (* Arrow *)
    destruct (lc_ty_at_arrow_inv (S k) A B Hlc) as [HlcA HlcB].
    split; intros [Hl [Hs H]].
    + split; [exact Hl | split; [exact Hs | intros u Hu]].
      apply (proj1 (IHB rho env k U P HlcB HU HP (tm_app t u))).
      apply H. apply (proj2 (IHA rho env k U P HlcA HU HP u)). exact Hu.
    + split; [exact Hl | split; [exact Hs | intros u Hu]].
      apply (proj2 (IHB rho env k U P HlcB HU HP (tm_app t u))).
      apply H. apply (proj1 (IHA rho env k U P HlcA HU HP u)). exact Hu.
  - (* All *)
    assert (HlcT0 : lc_ty_at (S (S k)) T0) by (apply (lc_ty_at_all_inv (S k) T0 Hlc)).
    split; intros [Hl [Hs H]].
    + split; [exact Hl | split; [exact Hs | intros Q U' HQ HU']].
      assert (HP' : forall s, P s <-> R rho (cons_env Q env) U s).
      { intro s. split; intro HPs.
        - apply (proj1 (R_closed_env_irrel U rho env (cons_env Q env) s HU)).
          apply (proj1 (HP s)). exact HPs.
        - apply (proj2 (HP s)).
          apply (proj2 (R_closed_env_irrel U rho env (cons_env Q env) s HU)). exact HPs. }
      apply (proj1 (IHT0 rho (cons_env Q env) (S k) U P HlcT0 HU HP' (tm_tapp t U'))).
      apply (proj1 (R_env_agree T0 rho (cons_env Q (set_env k P env))
                     (set_env (S k) P (cons_env Q env)) (S (S k)) HlcT0
                     (fun i Hi => cons_env_set_env Q P env k i) (tm_tapp t U'))).
      apply H; assumption.
    + split; [exact Hl | split; [exact Hs | intros Q U' HQ HU']].
      assert (HP' : forall s, P s <-> R rho (cons_env Q env) U s).
      { intro s. split; intro HPs.
        - apply (proj1 (R_closed_env_irrel U rho env (cons_env Q env) s HU)).
          apply (proj1 (HP s)). exact HPs.
        - apply (proj2 (HP s)).
          apply (proj2 (R_closed_env_irrel U rho env (cons_env Q env) s HU)). exact HPs. }
      apply (proj2 (R_env_agree T0 rho (cons_env Q (set_env k P env))
                     (set_env (S k) P (cons_env Q env)) (S (S k)) HlcT0
                     (fun i Hi => cons_env_set_env Q P env k i) (tm_tapp t U'))).
      apply (proj2 (IHT0 rho (cons_env Q env) (S k) U P HlcT0 HU HP' (tm_tapp t U'))).
      apply H; assumption.
  - (* Nat *) reflexivity.
Qed.

Lemma R_fvar_open_rec : forall T rho env k X P,
  lc_ty_at (S k) T ->
  ~ In X (fvars_ty T) ->
  forall t,
  R (update_rho rho X P) env (open_ty_rec k (Ty_FVar X) T) t <->
  R rho (set_env k P env) T t.
Proof.
  intros T. induction T as [ i | Y | A IHA B IHB | T0 IHT0 | ];
  intros rho env k X P Hlc Hfresh t; simpl in *.
  - (* BVar i *) destruct (Nat.eqb k i) eqn:E.
    + apply eqb_true_eq in E. subst i.
      unfold update_rho. simpl. rewrite Nat.eqb_refl.
      unfold set_env. simpl. rewrite Nat.eqb_refl. simpl. reflexivity.
    + assert (Hik : (i =? k) = false) by (apply eqb_false_sym; exact E).
      unfold set_env. simpl. rewrite Hik. simpl. reflexivity.
  - (* FVar Y *)
    assert (HYX : Y <> X).
    { intro Heq. apply Hfresh. subst Y. simpl. auto. }
    unfold update_rho. destruct (Nat.eqb Y X) eqn:E.
    + apply eqb_true_eq in E. contradiction.
    + reflexivity.
  - (* Arrow *)
    destruct (lc_ty_at_arrow_inv (S k) A B Hlc) as [HlcA HlcB].
    assert (HfA : ~ In X (fvars_ty A))
      by (apply not_in_app_l with (l2 := fvars_ty B); exact Hfresh).
    assert (HfB : ~ In X (fvars_ty B))
      by (apply not_in_app_r with (l1 := fvars_ty A); exact Hfresh).
    split; intros [Hl [Hs H]].
    + split; [exact Hl | split; [exact Hs | intros u Hu]].
      apply (proj1 (IHB rho env k X P HlcB HfB (tm_app t u))).
      apply H. apply (proj2 (IHA rho env k X P HlcA HfA u)). exact Hu.
    + split; [exact Hl | split; [exact Hs | intros u Hu]].
      apply (proj2 (IHB rho env k X P HlcB HfB (tm_app t u))).
      apply H. apply (proj1 (IHA rho env k X P HlcA HfA u)). exact Hu.
  - (* All *)
    assert (HlcT0 : lc_ty_at (S (S k)) T0) by (apply (lc_ty_at_all_inv (S k) T0 Hlc)).
    assert (HfT0 : ~ In X (fvars_ty T0)) by exact Hfresh.
    split; intros [Hl [Hs H]].
    + split; [exact Hl | split; [exact Hs | intros Q U' HQ HU']].
      apply (proj2 (R_env_agree T0 rho (cons_env Q (set_env k P env))
                     (set_env (S k) P (cons_env Q env)) (S (S k)) HlcT0
                     (fun i Hi => cons_env_set_env Q P env k i) (tm_tapp t U'))).
      apply (proj1 (IHT0 rho (cons_env Q env) (S k) X P HlcT0 HfT0 (tm_tapp t U'))).
      apply H; assumption.
    + split; [exact Hl | split; [exact Hs | intros Q U' HQ HU']].
      apply (proj2 (IHT0 rho (cons_env Q env) (S k) X P HlcT0 HfT0 (tm_tapp t U'))).
      apply (proj1 (R_env_agree T0 rho (cons_env Q (set_env k P env))
                     (set_env (S k) P (cons_env Q env)) (S (S k)) HlcT0
                     (fun i Hi => cons_env_set_env Q P env k i) (tm_tapp t U'))).
      apply H; assumption.
  - (* Nat *) reflexivity.
Qed.

Lemma IsCand_R : forall T rho env,
  (forall X, IsCand (rho X)) ->
  (forall i, IsCand (env i)) ->
  IsCand (R rho env T).
Proof.
  induction T as [ i | X | A IHA B IHB | T0 IHT0 | ];
  intros rho env Hrho Henv; simpl.
  - (* BVar *) exact (Henv i).
  - (* FVar *) exact (Hrho X).
  - (* Arrow *)
    destruct (IHA rho env Hrho Henv) as [Alc [Asn [Acr2 [Aexp Aann]]]].
    destruct (IHB rho env Hrho Henv) as [Blc [Bsn [Bcr2 [Bexp Bann]]]].
    split.
    + intros t [Hl _]. exact Hl.
    + split.
      * intros t [_ [Hs _]]. exact Hs.
      * split.
        -- intros t t' [Hl [Hs H]] Hstep.
           split.
           ++ apply lc_tm_step with t; assumption.
           ++ split.
              ** apply SN_step with t; assumption.
              ** intros u Hu.
                 apply Bcr2 with (tm_app t u).
                 --- apply H; exact Hu.
                 --- apply ST_App1; [exact Hstep | apply Alc; exact Hu].
        -- split.
           ++ intros t Hnv Hl Hs Hred.
              split.
              ** exact Hl.
              ** split.
                 --- exact Hs.
                 --- intros u Hu.
                     assert (Hreds : forall w, step (tm_app t u) w -> R rho env B w).
                     { intros w Hw. inversion Hw; subst.
                       - (* AppAbs *) exfalso. apply Hnv. apply v_abs. assumption.
                       - (* App1 *)
                         match goal with
                         | Hst : step t ?w0 |- _ =>
                             destruct (Hred w0 Hst) as [_ [_ Happ]]; apply Happ; exact Hu
                         end.
                       - (* App2 *) exfalso. apply Hnv. assumption.
                     }
                     apply Bexp.
                     *** intro Hv. exact (value_app_absurd t u Hv).
                     *** apply lc_tm_app; [exact Hl | apply Alc; exact Hu].
                     *** apply SN_intro. intros w Hw. apply Bsn. apply Hreds. exact Hw.
                     *** exact Hreds.
           ++ intros t t' He Hl Hl'.
              split; intros [Hl0 [Hs0 H]].
              ** split; [exact Hl' | split; [apply (proj1 (erase_sn t t' He Hl Hl')); exact Hs0 | intros u Hu]].
                 apply (proj1 (Bann (tm_app t u) (tm_app t' u)
                   ltac:(simpl; rewrite He; reflexivity)
                   ltac:(apply (lc_tm_app 0 0 t u); [exact Hl | apply Alc; exact Hu])
                   ltac:(apply (lc_tm_app 0 0 t' u); [exact Hl' | apply Alc; exact Hu]))).
                 apply H; exact Hu.
              ** split; [exact Hl | split; [apply (proj2 (erase_sn t t' He Hl Hl')); exact Hs0 | intros u Hu]].
                 apply (proj2 (Bann (tm_app t u) (tm_app t' u)
                   ltac:(simpl; rewrite He; reflexivity)
                   ltac:(apply (lc_tm_app 0 0 t u); [exact Hl | apply Alc; exact Hu])
                   ltac:(apply (lc_tm_app 0 0 t' u); [exact Hl' | apply Alc; exact Hu]))).
                 apply H; exact Hu.
  - (* All *)
    split.
    + intros t [Hl _]. exact Hl.
    + split.
      * intros t [_ [Hs _]]. exact Hs.
      * split.
        -- intros t t' [Hl [Hs H]] Hstep.
           split.
           ++ apply lc_tm_step with t; assumption.
           ++ split.
              ** apply SN_step with t; assumption.
              ** intros P U HP HU.
                 assert (Hc : IsCand (R rho (cons_env P env) T0)).
                 { apply IHT0.
                   - exact Hrho.
                   - intros j. destruct j as [| j]; simpl.
                     + exact HP.
                     + apply Henv. }
                 destruct Hc as [_ [_ [T0cr2 _]]].
                 apply T0cr2 with (tm_tapp t U).
                 --- apply H; assumption.
                 --- apply ST_TApp; [exact Hstep | exact HU].
        -- split.
           ++ intros t Hnv Hl Hs Hred.
              split.
              ** exact Hl.
              ** split.
                 --- exact Hs.
                 --- intros P U HP HU.
                     assert (Hc : IsCand (R rho (cons_env P env) T0)).
                     { apply IHT0.
                       - exact Hrho.
                       - intros j. destruct j as [| j]; simpl.
                         + exact HP.
                         + apply Henv. }
                     destruct Hc as [_ [T0sn [_ [T0exp _]]]].
                     assert (Hreds : forall w, step (tm_tapp t U) w ->
                                                 R rho (cons_env P env) T0 w).
                     { intros w Hw. inversion Hw; subst.
                       - (* TAppTabs *) exfalso. apply Hnv. apply v_tabs. assumption.
                       - (* TApp *)
                         match goal with
                         | Hst : step t ?w0 |- _ =>
                             destruct (Hred w0 Hst) as [_ [_ HAll]]; apply (HAll P U HP HU)
                         end.
                     }
                     apply T0exp.
                     *** intro Hv. exact (value_tapp_absurd t U Hv).
                     *** apply lc_tm_tapp; [exact Hl | exact HU].
                     *** apply SN_intro. intros w Hw. apply T0sn. apply Hreds. exact Hw.
                     *** exact Hreds.
           ++ intros t t' He Hl Hl'.
              split; intros [Hl0 [Hs0 H]].
              ** split; [exact Hl' | split; [apply (proj1 (erase_sn t t' He Hl Hl')); exact Hs0 | intros P U HP HU]].
                 assert (Hc : IsCand (R rho (cons_env P env) T0)).
                 { apply IHT0.
                   - exact Hrho.
                   - intros j. destruct j as [| j]; simpl.
                     + exact HP.
                     + apply Henv. }
                 destruct Hc as [_ [_ [_ [_ T0ann]]]].
                 apply (proj1 (T0ann (tm_tapp t U) (tm_tapp t' U)
                   ltac:(simpl; rewrite He; reflexivity)
                   ltac:(apply (lc_tm_tapp 0 0 t U); [exact Hl | exact HU])
                   ltac:(apply (lc_tm_tapp 0 0 t' U); [exact Hl' | exact HU]))).
                 apply H; assumption.
              ** split; [exact Hl | split; [apply (proj2 (erase_sn t t' He Hl Hl')); exact Hs0 | intros P U HP HU]].
                 assert (Hc : IsCand (R rho (cons_env P env) T0)).
                 { apply IHT0.
                   - exact Hrho.
                   - intros j. destruct j as [| j]; simpl.
                     + exact HP.
                     + apply Henv. }
                 destruct Hc as [_ [_ [_ [_ T0ann]]]].
                 apply (proj2 (T0ann (tm_tapp t U) (tm_tapp t' U)
                   ltac:(simpl; rewrite He; reflexivity)
                   ltac:(apply (lc_tm_tapp 0 0 t U); [exact Hl | exact HU])
                   ltac:(apply (lc_tm_tapp 0 0 t' U); [exact Hl' | exact HU]))).
                 apply H; assumption.
  - (* Nat *)
    split.
    + intros t [Hl _]. exact Hl.
    + split.
      * intros t [_ Hs]. exact Hs.
      * split.
        -- intros t t' [Hl Hs] Hstep. split.
           ++ apply lc_tm_step with t; assumption.
           ++ apply SN_step with t; assumption.
        -- split.
           ++ intros t Hnv Hl Hs Hred. split; assumption.
           ++ intros t t' He Hl Hl'. split; intros [_ Hs].
              ** split; [exact Hl' | apply (proj1 (erase_sn t t' He Hl Hl')); exact Hs].
              ** split; [exact Hl | apply (proj2 (erase_sn t t' He Hl Hl')); exact Hs].
Qed.

Lemma R_fvar : forall T rho env x,
  (forall X, IsCand (rho X)) ->
  (forall i, IsCand (env i)) ->
  R rho env T (tm_fvar x).
Proof.
  intros T rho env x Hrho Henv.
  destruct (IsCand_R T rho env Hrho Henv) as [Hlc [Hsn [Hcr2 [Hexp Hann]]]].
  apply Hexp.
  - intro Hv. exact (value_fvar_absurd x Hv).
  - apply lc_tm_fvar.
  - apply SN_intro. intros u Hu. inversion Hu.
  - intros t' Hstep. inversion Hstep.
Qed.

Lemma R_app_abs : forall T1 T2 body u rho env,
  (forall X, IsCand (rho X)) ->
  (forall i, IsCand (env i)) ->
  locally_closed_tm (tm_abs T1 body) ->
  (forall v, R rho env T1 v -> R rho env T2 (open_tm body v)) ->
  R rho env T1 u ->
  R rho env T2 (tm_app (tm_abs T1 body) u).
Proof.
  intros T1 T2 body u rho env Hrho Henv Hlcabs Hbody Hu.
  destruct (IsCand_R T1 rho env Hrho Henv) as [T1lc [T1sn [T1cr2 [T1exp T1ann]]]].
  destruct (IsCand_R T2 rho env Hrho Henv) as [T2lc [T2sn [T2cr2 [T2exp T2ann]]]].
  assert (Hsn : strongly_normalizing u) by (apply T1sn; exact Hu).
  revert Hu. induction Hsn as [u0 Hred IH].
  intros Hu.
  assert (Hreds : forall w, step (tm_app (tm_abs T1 body) u0) w -> R rho env T2 w).
  { intros w Hw. inversion Hw; subst.
    - apply Hbody. exact Hu.
    - match goal with H : step (tm_abs T1 body) _ |- _ => inversion H end.
    - match goal with
      | Hst : ?x --> ?y |- R _ _ _ (tm_app _ ?y) =>
          exact (IH y Hst (T1cr2 u0 y Hu Hst))
      end.
  }
  apply T2exp.
  - intro Hv. exact (value_app_absurd (tm_abs T1 body) u0 Hv).
  - apply (lc_tm_app 0 0 (tm_abs T1 body) u0); [exact Hlcabs | apply T1lc; exact Hu].
  - apply SN_intro. intros w Hw. apply T2sn. apply Hreds. exact Hw.
  - exact Hreds.
Qed.

Lemma R_natrec_zero : forall T rho env b s,
  (forall X, IsCand (rho X)) ->
  (forall i, IsCand (env i)) ->
  R rho env T b ->
  R rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  R rho env T (tm_natrec tm_zero b s).
Proof.
  intros T rho env b s Hrho Henv Hb Hs.
  destruct (IsCand_R T rho env Hrho Henv) as [Tlc [Tsn [Tcr2 [Texp Tann]]]].
  destruct (IsCand_R Ty_Nat rho env Hrho Henv) as [Nlc [Nsn [Ncr2 [Nexp Nann]]]].
  destruct (IsCand_R (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho env Hrho Henv)
    as [Alc [Asn [Acr2 [Aexp Aann]]]].
  assert (Hsb : strongly_normalizing b) by (apply Tsn; exact Hb).
  revert Hb Hs.
  generalize dependent s.
  induction Hsb as [b0 Hredb IHb].
  intros s Hb Hs.
  assert (Hss : strongly_normalizing s) by (apply Asn; exact Hs).
  revert Hs.
  induction Hss as [s0 Hreds IHs].
  intros Hs.
  assert (Hred_all : forall w, step (tm_natrec tm_zero b0 s0) w -> R rho env T w).
  { intros w Hw. inversion Hw; subst.
    - match goal with H : step tm_zero _ |- _ => inversion H end.
    - match goal with Hst : step b0 ?b1 |- _ =>
        exact (IHb b1 Hst s0 (Tcr2 b0 b1 Hb Hst) Hs) end.
    - match goal with Hst : step s0 ?s1 |- _ =>
        exact (IHs s1 Hst (Acr2 s0 s1 Hs Hst)) end.
    - exact Hb.
  }
  apply Texp.
  - intro Hv. exact (value_natrec_absurd tm_zero b0 s0 Hv).
  - apply (lc_tm_rec 0 0 tm_zero b0 s0);
      [apply lc_tm_zero | apply Tlc; exact Hb | apply Alc; exact Hs].
  - apply SN_intro. intros w Hw. apply Tsn. apply Hred_all. exact Hw.
  - exact Hred_all.
Qed.

Lemma R_natrec_succ : forall T rho env m b s,
  (forall X, IsCand (rho X)) ->
  (forall i, IsCand (env i)) ->
  numeric_value m ->
  (forall b s, R rho env Ty_Nat m -> R rho env T b ->
     R rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s -> R rho env T (tm_natrec m b s)) ->
  R rho env Ty_Nat (tm_succ m) ->
  R rho env T b ->
  R rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  R rho env T (tm_natrec (tm_succ m) b s).
Proof.
  intros T rho env m b s Hrho Henv Hm IHm HnR Hb Hs.
  destruct (IsCand_R T rho env Hrho Henv) as [Tlc [Tsn [Tcr2 [Texp Tann]]]].
  destruct (IsCand_R Ty_Nat rho env Hrho Henv) as [Nlc [Nsn [Ncr2 [Nexp Nann]]]].
  destruct (IsCand_R (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho env Hrho Henv)
    as [Alc [Asn [Acr2 [Aexp Aann]]]].
  assert (Hsb : strongly_normalizing b) by (apply Tsn; exact Hb).
  revert Hb Hs.
  generalize dependent s.
  induction Hsb as [b0 Hredb IHb].
  intros s Hb Hs.
  assert (Hss : strongly_normalizing s) by (apply Asn; exact Hs).
  revert Hs.
  induction Hss as [s0 Hreds IHs].
  intros Hs.
  assert (Hred_all : forall w, step (tm_natrec (tm_succ m) b0 s0) w -> R rho env T w).
  { intros w Hw. inversion Hw; subst.
    - (* RecArg *) match goal with H : step (tm_succ m) _ |- _ =>
        exfalso; exact (numeric_value_no_step (tm_succ m) (nv_succ m Hm) _ H) end.
    - (* RecBase *) match goal with Hst : step b0 ?b1 |- _ =>
        exact (IHb b1 Hst s0 (Tcr2 b0 b1 Hb Hst) Hs) end.
    - (* RecStep *) match goal with Hst : step s0 ?s1 |- _ =>
        exact (IHs s1 Hst (Acr2 s0 s1 Hs Hst)) end.
    - (* RecSucc *)
      match goal with
      | |- R _ _ _ (tm_app (tm_app s0 m) (tm_natrec m b0 s0)) =>
          assert (Rm : R rho env Ty_Nat m)
            by (split; [apply numeric_value_lc; exact Hm
                       | apply numeric_value_sn; exact Hm]);
          assert (Hrec : R rho env T (tm_natrec m b0 s0))
            by (apply (IHm b0 s0 Rm Hb Hs));
          destruct Hs as [_ [_ Hsapp]];
          destruct (Hsapp m Rm) as [_ [_ Hrecapp]];
          apply (Hrecapp (tm_natrec m b0 s0) Hrec)
      end.
  }
  apply Texp.
  - intro Hv. exact (value_natrec_absurd (tm_succ m) b0 s0 Hv).
  - apply (lc_tm_rec 0 0 (tm_succ m) b0 s0);
      [apply (lc_tm_succ 0 0 m); apply numeric_value_lc; exact Hm
      | apply Tlc; exact Hb | apply Alc; exact Hs].
  - apply SN_intro. intros w Hw. apply Tsn. apply Hred_all. exact Hw.
  - exact Hred_all.
Qed.

Lemma R_natrec_num : forall T rho env,
  (forall X, IsCand (rho X)) ->
  (forall i, IsCand (env i)) ->
  forall n, numeric_value n ->
  forall b s,
    R rho env Ty_Nat n ->
    R rho env T b ->
    R rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    R rho env T (tm_natrec n b s).
Proof.
  intros T rho env Hrho Henv n Hnv.
  induction Hnv as [| m Hm IHm]; intros b s HnR Hb Hs.
  - apply (R_natrec_zero T rho env b s); assumption.
  - apply (R_natrec_succ T rho env m b s Hrho Henv Hm IHm HnR Hb Hs).
Qed.

Lemma R_natrec_gen : forall T rho env,
  (forall X, IsCand (rho X)) ->
  (forall i, IsCand (env i)) ->
  forall n, strongly_normalizing n ->
  forall b s,
    R rho env Ty_Nat n ->
    R rho env T b ->
    R rho env (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
    R rho env T (tm_natrec n b s).
Proof.
  intros T rho env Hrho Henv n Hsn.
  induction Hsn as [n Hred IH].
  intros b s HnR Hb Hs.
  destruct (IsCand_R T rho env Hrho Henv) as [Tlc [Tsn [Tcr2 [Texp Tann]]]].
  destruct (IsCand_R Ty_Nat rho env Hrho Henv) as [Nlc [Nsn [Ncr2 [Nexp Nann]]]].
  destruct (IsCand_R (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho env Hrho Henv)
    as [Alc [Asn [Acr2 [Aexp Aann]]]].
  assert (Hred_all : forall w, step (tm_natrec n b s) w -> R rho env T w).
  { intros w Hw. inversion Hw; subst.
    - (* RecArg *) match goal with Hst : step n ?n1 |- _ =>
        exact (IH n1 Hst b s (Ncr2 n n1 HnR Hst) Hb Hs) end.
    - (* RecBase *) match goal with
      | Hst : step b ?b1, Hnum : numeric_value n |- _ =>
          exact (R_natrec_num T rho env Hrho Henv n Hnum b1 s HnR
                   (Tcr2 b b1 Hb Hst) Hs)
      end.
    - (* RecStep *) match goal with
      | Hst : step s ?s1, Hnum : numeric_value n |- _ =>
          exact (R_natrec_num T rho env Hrho Henv n Hnum b s1 HnR Hb
                   (Acr2 s s1 Hs Hst))
      end.
    - exact Hb.
    - (* RecSucc *)
      match goal with
      | Hnum : numeric_value ?mm |- R _ _ _ (tm_app (tm_app s ?mm) (tm_natrec ?mm b s)) =>
          assert (Rm : R rho env Ty_Nat mm)
            by (split; [apply numeric_value_lc; exact Hnum
                       | apply numeric_value_sn; exact Hnum]);
          assert (Hrec : R rho env T (tm_natrec mm b s))
            by (apply (R_natrec_num T rho env Hrho Henv mm Hnum b s Rm Hb Hs));
          destruct Hs as [_ [_ Hsapp]];
          destruct (Hsapp mm Rm) as [_ [_ Hrecapp]];
          apply (Hrecapp (tm_natrec mm b s) Hrec)
      end.
  }
  apply Texp.
  - intro Hv. exact (value_natrec_absurd n b s Hv).
  - apply (lc_tm_rec 0 0 n b s); [apply Nlc; exact HnR | apply Tlc; exact Hb | apply Alc; exact Hs].
  - apply SN_intro. intros w Hw. apply Tsn. apply Hred_all. exact Hw.
  - exact Hred_all.
Qed.

Lemma lookup_update_eq : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof.
  intros Gamma x T. unfold update. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_update_neq : forall Gamma x y T,
  y <> x -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros Gamma x y T Hyx. unfold update. simpl.
  destruct (Nat.eqb y x) eqn:E.
  - apply eqb_true_eq in E. exfalso. apply Hyx. exact E.
  - reflexivity.
Qed.

Lemma env_rel_update : forall Gamma rho env sigma x T1 u,
  (forall y U, lookup_context y Gamma = Some U -> R rho env U (sigma y)) ->
  R rho env T1 u ->
  forall y U, lookup_context y (update Gamma x T1) = Some U ->
              R rho env U (update_sigma sigma x u y).
Proof.
  intros Gamma rho env sigma x T1 u HGamma Hu y U Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - apply eqb_true_eq in E. subst y.
    rewrite lookup_update_eq in Hlook. injection Hlook as HUT. subst U.
    unfold update_sigma. simpl. rewrite Nat.eqb_refl. exact Hu.
  - assert (Hyx : y <> x) by (apply eqb_false_neq; exact E).
    rewrite lookup_update_neq in Hlook by exact Hyx.
    unfold update_sigma. simpl. rewrite E. apply HGamma. exact Hlook.
Qed.

Lemma sigma_lc_update : forall sigma x u,
  (forall y, locally_closed_tm (sigma y)) ->
  locally_closed_tm u ->
  forall y, locally_closed_tm (update_sigma sigma x u y).
Proof.
  intros sigma x u Hsig Hu y. unfold update_sigma.
  destruct (Nat.eqb y x); auto.
Qed.

Lemma update_rho_proper : forall rho X P,
  (forall Y, IsCand (rho Y)) -> IsCand P ->
  (forall Y, IsCand (update_rho rho X P Y)).
Proof.
  intros rho X P Hrho HP Y. unfold update_rho.
  destruct (Nat.eqb Y X); auto.
Qed.

Lemma cons_env_proper : forall P env,
  IsCand P -> (forall i, IsCand (env i)) ->
  (forall i, IsCand (cons_env P env i)).
Proof.
  intros P env HP Henv i. destruct i as [| j]; simpl; [exact HP | apply Henv].
Qed.

Fixpoint fvars_context (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => fvars_ty T ++ fvars_context Gamma'
  end.

Lemma lookup_in_context_snd : forall Gamma y U,
  lookup_context y Gamma = Some U -> In U (map snd Gamma).
Proof.
  induction Gamma as [|[z T] Gamma IH]; intros y U H; simpl in H.
  - discriminate.
  - destruct (Nat.eqb y z) eqn:E.
    + apply eqb_true_eq in E. subst z.
      injection H as HU. subst U. simpl. auto.
    + simpl. right. exact (IH y U H).
Qed.

Lemma fvars_context_spec : forall Gamma U,
  In U (map snd Gamma) -> forall X, In X (fvars_ty U) -> In X (fvars_context Gamma).
Proof.
  induction Gamma as [|[z T] Gamma IH]; intros U Hin X Hx; simpl in *.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + apply in_app_iff. left. exact Hx.
    + apply in_app_iff. right. exact (IH U Hin X Hx).
Qed.

Lemma fvars_context_lookup : forall Gamma y U X,
  ~ In X (fvars_context Gamma) -> lookup_context y Gamma = Some U ->
  ~ In X (fvars_ty U).
Proof.
  intros Gamma y U X Hctx Hlook Hx.
  apply Hctx. exact (fvars_context_spec Gamma U (lookup_in_context_snd Gamma y U Hlook) X Hx).
Qed.

Lemma R_rho_agree_X : forall T rho X P,
  ~ In X (fvars_ty T) ->
  forall env t, R (update_rho rho X P) env T t <-> R rho env T t.
Proof.
  induction T as [ i | Y | A IHA B IHB | T0 IHT0 | ];
  intros rho X P Hfresh env t; simpl in *.
  - reflexivity.
  - assert (HYX : Y <> X).
    { intro Heq. apply Hfresh. subst Y. simpl. auto. }
    unfold update_rho. destruct (Nat.eqb Y X) eqn:E.
    + apply eqb_true_eq in E. contradiction.
    + reflexivity.
  - assert (HfA : ~ In X (fvars_ty A))
      by (apply not_in_app_l with (l2 := fvars_ty B); exact Hfresh).
    assert (HfB : ~ In X (fvars_ty B))
      by (apply not_in_app_r with (l1 := fvars_ty A); exact Hfresh).
    split; intros [Hl [Hs H]].
    + split; [exact Hl | split; [exact Hs | intros u Hu]].
      apply (proj1 (IHB rho X P HfB env (tm_app t u))).
      apply H. apply (proj2 (IHA rho X P HfA env u)). exact Hu.
    + split; [exact Hl | split; [exact Hs | intros u Hu]].
      apply (proj2 (IHB rho X P HfB env (tm_app t u))).
      apply H. apply (proj1 (IHA rho X P HfA env u)). exact Hu.
  - assert (HfT0 : ~ In X (fvars_ty T0)) by exact Hfresh.
    split; intros [Hl [Hs H]].
    + split; [exact Hl | split; [exact Hs | intros Q U HQ HU]].
      apply (proj1 (IHT0 rho X P HfT0 (cons_env Q env) (tm_tapp t U))).
      apply H; assumption.
    + split; [exact Hl | split; [exact Hs | intros Q U HQ HU]].
      apply (proj2 (IHT0 rho X P HfT0 (cons_env Q env) (tm_tapp t U))).
      apply H; assumption.
  - reflexivity.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho env sigma,
    (forall X, IsCand (rho X)) ->
    (forall i, IsCand (env i)) ->
    (forall y, locally_closed_tm (sigma y)) ->
    (forall x U, lookup_context x Gamma = Some U -> R rho env U (sigma x)) ->
    R rho env T (subst_all sigma t).
Proof.
  intros Delta Gamma t T Hty.
  induction Hty as
    [ Delta Gamma x T Hlook Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hbody IHbody
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hbody IHbody
    | Delta Gamma t T U H1 IH1 HwfU
    | Delta Gamma
    | Delta Gamma n Hn IHn
    | Delta Gamma n b s T Hn IHn Hb IHb Hs IHs ];
  intros rho env sigma Hrho Henv Hsig HGamma.
  - (* T_Var *) apply HGamma with (x := x) (U := T). exact Hlook.
  - (* T_Abs *)
    simpl.
    set (body := subst_all sigma t2).
    set (x := fresh_atom (L ++ fvars_tm t2)).
    assert (HxL : ~ In x L).
    { intro Hin. apply (fresh_atom_not_in (L ++ fvars_tm t2)). apply in_or_app. left. exact Hin. }
    assert (HxFV : ~ In x (fvars_tm t2)).
    { intro Hin. apply (fresh_atom_not_in (L ++ fvars_tm t2)). apply in_or_app. right. exact Hin. }
    assert (HT1lc : lc_ty_at 0 T1) by (apply wf_ty_lc with (Delta := Delta); exact Hwf).
    (* body lc at depth 1 *)
    assert (Hbody_lc : lc_tm_at 0 1 body).
    { set (sigma_x := update_sigma sigma x (tm_fvar x)).
      assert (Hsigx : forall y, locally_closed_tm (sigma_x y))
        by (apply sigma_lc_update; [exact Hsig | apply lc_tm_fvar]).
      assert (Hrelx : forall y U, lookup_context y (update Gamma x T1) = Some U ->
                                  R rho env U (sigma_x y)).
      { apply env_rel_update; [exact HGamma | apply R_fvar; assumption]. }
      specialize (IHbody x HxL rho env sigma_x Hrho Henv Hsigx Hrelx).
      assert (Heq : subst_all sigma_x (open_tm t2 (tm_fvar x)) =
                    open_tm body (tm_fvar x)).
      { unfold body. unfold open_tm.
        apply (subst_all_open_tm_fvar_rec sigma x (tm_fvar x) t2 Hsig HxFV 0). }
      rewrite Heq in IHbody.
      pose proof (IsCand_R T2 rho env Hrho Henv) as Hc2.
      destruct Hc2 as [T2lc _].
      apply (lc_tm_open_back 0 0 body x).
      apply T2lc. exact IHbody. }
    assert (Hlcabs : locally_closed_tm (tm_abs T1 body)).
    { apply (lc_tm_abs 0 0 T1 body); assumption. }
    assert (Hbody_sem : forall u, R rho env T1 u -> R rho env T2 (open_tm body u)).
    { intros u Hu.
      set (sigma_u := update_sigma sigma x u).
      assert (Hsigu : forall y, locally_closed_tm (sigma_u y)).
      { apply sigma_lc_update; [exact Hsig |].
        pose proof (IsCand_R T1 rho env Hrho Henv) as Hc1.
        destruct Hc1 as [T1lc _]. apply T1lc. exact Hu. }
      assert (Hrelu : forall y U, lookup_context y (update Gamma x T1) = Some U ->
                                  R rho env U (sigma_u y)).
      { apply env_rel_update; [exact HGamma | exact Hu]. }
      specialize (IHbody x HxL rho env sigma_u Hrho Henv Hsigu Hrelu).
      assert (Heq : subst_all sigma_u (open_tm t2 (tm_fvar x)) = open_tm body u).
      { unfold body. unfold open_tm.
        apply (subst_all_open_tm_fvar_rec sigma x u t2 Hsig HxFV 0). }
      rewrite Heq in IHbody. exact IHbody. }
    split.
    + exact Hlcabs.
    + split.
      * apply SN_abs.
      * intros u Hu.
        apply (R_app_abs T1 T2 body u rho env Hrho Henv Hlcabs Hbody_sem Hu).
  - (* T_App *)
    specialize (IH1 rho env sigma Hrho Henv Hsig HGamma).
    specialize (IH2 rho env sigma Hrho Henv Hsig HGamma).
    simpl. destruct IH1 as [Hlc1 [Hsn1 Happ]].
    apply Happ. exact IH2.
  - (* T_TAbs *)
    simpl.
    set (body := subst_all sigma t).
    set (X := fresh_atom (L ++ fvars_ty T ++ fvars_context Gamma)).
    assert (HXL : ~ In X L).
    { intro Hin. apply (fresh_atom_not_in (L ++ fvars_ty T ++ fvars_context Gamma)).
      apply in_app_iff. left. exact Hin. }
    assert (HXFV : ~ In X (fvars_ty T)).
    { intro Hin. apply (fresh_atom_not_in (L ++ fvars_ty T ++ fvars_context Gamma)).
      apply in_app_iff. right. apply in_app_iff. left. exact Hin. }
    assert (HXctx : ~ In X (fvars_context Gamma)).
    { intro Hin. apply (fresh_atom_not_in (L ++ fvars_ty T ++ fvars_context Gamma)).
      apply in_app_iff. right. apply in_app_iff. right. exact Hin. }
    pose proof (has_type_lc_ty Delta Gamma (tm_tabs t) (Ty_All T)
                  (T_TAbs L Delta Gamma t T Hbody)) as HlcAll.
    assert (HlcT : lc_ty_at 1 T) by (apply (lc_ty_at_all_inv 0 T); exact HlcAll).
    (* body lc at type depth 1 *)
    assert (Hbody_lc : lc_tm_at 1 0 body).
    { set (P0 := R rho env Ty_Nat).
      assert (HP0 : IsCand P0) by (apply IsCand_R; assumption).
      set (rho0 := update_rho rho X P0).
      assert (Hrho0 : forall Y, IsCand (rho0 Y))
        by (apply update_rho_proper; assumption).
      assert (HGamma0 : forall y U, lookup_context y Gamma = Some U ->
                                    R rho0 env U (sigma y)).
      { intros y U Hlk.
        apply (proj2 (R_rho_agree_X U rho X P0
                       (fvars_context_lookup Gamma y U X HXctx Hlk) env (sigma y))).
        apply HGamma. exact Hlk. }
      specialize (IHbody X HXL rho0 env sigma Hrho0 Henv Hsig HGamma0).
      assert (Heq : subst_all sigma (open_tm_ty t (Ty_FVar X)) =
                    open_tm_ty body (Ty_FVar X)).
      { unfold body. unfold open_tm_ty.
        apply (subst_all_open_tm_ty_lc sigma Hsig 0 (Ty_FVar X) t). }
      rewrite Heq in IHbody.
      pose proof (IsCand_R (open_ty T (Ty_FVar X)) rho0 env Hrho0 Henv) as Hc.
      destruct Hc as [Hlcx _].
      apply (lc_tm_ty_open_back 0 0 body X). simpl. apply Hlcx. exact IHbody. }
    assert (Hlctabs : locally_closed_tm (tm_tabs body)).
    { apply (lc_tm_tabs 0 0 body); assumption. }
    split.
    + exact Hlctabs.
    + split.
      * apply SN_tabs.
      * intros P U HP HU.
        (* obtain the body relation at this P *)
        set (rho1 := update_rho rho X P).
        assert (Hrho1 : forall Y, IsCand (rho1 Y))
          by (apply update_rho_proper; assumption).
        assert (HGamma1 : forall y U0, lookup_context y Gamma = Some U0 ->
                                      R rho1 env U0 (sigma y)).
        { intros y U0 Hlk.
          apply (proj2 (R_rho_agree_X U0 rho X P
                         (fvars_context_lookup Gamma y U0 X HXctx Hlk) env (sigma y))).
          apply HGamma. exact Hlk. }
        specialize (IHbody X HXL rho1 env sigma Hrho1 Henv Hsig HGamma1).
        assert (Heq : subst_all sigma (open_tm_ty t (Ty_FVar X)) =
                      open_tm_ty body (Ty_FVar X)).
        { unfold body. unfold open_tm_ty.
          apply (subst_all_open_tm_ty_lc sigma Hsig 0 (Ty_FVar X) t). }
        rewrite Heq in IHbody.
        (* move from rho1 to set_env 0 P env *)
        assert (Hset : R rho (set_env 0 P env) T (open_tm_ty body (Ty_FVar X))).
        { apply (proj1 (R_fvar_open_rec T rho env 0 X P HlcT HXFV
                          (open_tm_ty body (Ty_FVar X)))).
          unfold rho1 in IHbody. exact IHbody. }
        (* move from set_env to cons_env *)
        assert (Hcons : R rho (cons_env P env) T (open_tm_ty body (Ty_FVar X))).
        { apply (proj1 (R_env_agree T rho (set_env 0 P env) (cons_env P env) 1 HlcT
      ltac:(intros i Hi; assert (Hi0 : i = 0) by lia; subst i; reflexivity)
      (open_tm_ty body (Ty_FVar X)))).
    exact Hset. }
        (* annotation invariance: FVar X -> U *)
        pose proof (IsCand_R T rho (cons_env P env) Hrho
                      (cons_env_proper P env HP Henv)) as HcT.
        destruct HcT as [_ [_ [_ [_ Tann]]]].
        assert (Hann : R rho (cons_env P env) T (open_tm_ty body U)).
        { apply (proj1 (Tann (open_tm_ty body (Ty_FVar X)) (open_tm_ty body U)
      ltac:(unfold open_tm_ty; rewrite !erase_tm_open_tm_ty; reflexivity)
      ltac:(apply (lc_tm_ty_open 0 0 body (Ty_FVar X)); [exact Hbody_lc | apply lc_ty_fvar])
      ltac:(apply (lc_tm_ty_open 0 0 body U); [exact Hbody_lc | exact HU]))).
    exact Hcons. }
        (* expansion of the type application *)
        pose proof (IsCand_R T rho (cons_env P env) Hrho
                      (cons_env_proper P env HP Henv)) as HcT2.
        destruct HcT2 as [_ [Tsn [_ [Texp _]]]].
        assert (Hreds : forall w, step (tm_tapp (tm_tabs body) U) w ->
                                   R rho (cons_env P env) T w).
        { intros w Hw. inversion Hw; subst.
          - exact Hann.
          - match goal with Hst : step (tm_tabs body) _ |- _ => inversion Hst end. }
        apply Texp.
        -- intro Hv. exact (value_tapp_absurd (tm_tabs body) U Hv).
        -- apply (lc_tm_tapp 0 0 (tm_tabs body) U); [exact Hlctabs | exact HU].
        -- apply SN_intro. intros w Hw. apply Tsn. apply Hreds. exact Hw.
        -- exact Hreds.
  - (* T_TApp *)
    simpl.
    pose proof (has_type_lc_ty Delta Gamma t (Ty_All T) H1) as HlcAll.
    assert (HlcT : lc_ty_at 1 T) by (apply (lc_ty_at_all_inv 0 T); exact HlcAll).
    assert (HlcU : locally_closed_ty U) by (apply wf_ty_lc with (Delta := Delta); exact HwfU).
    set (PU := R rho env U).
    assert (HPU : IsCand PU) by (apply IsCand_R; assumption).
    specialize (IH1 rho env sigma Hrho Henv Hsig HGamma).
    destruct IH1 as [_ [_ HAll]].
    assert (Hcons : R rho (cons_env PU env) T (tm_tapp (subst_all sigma t) U)).
    { apply (HAll PU U HPU HlcU). }
    assert (Hset : R rho (set_env 0 PU env) T (tm_tapp (subst_all sigma t) U)).
    { apply (proj2 (R_env_agree T rho (set_env 0 PU env) (cons_env PU env) 1 HlcT
        ltac:(intros i Hi; assert (Hi0 : i = 0) by lia; subst i; reflexivity)
        (tm_tapp (subst_all sigma t) U))).
      exact Hcons. }
    apply (proj1 (R_ty_open_rec T rho env 0 U PU HlcT HlcU
                    (fun s => conj (fun Hs => Hs) (fun Hs => Hs))
                    (tm_tapp (subst_all sigma t) U))).
    exact Hset.
  - (* T_Zero *)
    simpl. split.
    + apply lc_tm_zero.
    + apply SN_intro. intros u Hu. inversion Hu.
  - (* T_Succ *)
    specialize (IHn rho env sigma Hrho Henv Hsig HGamma).
    simpl. destruct IHn as [Hlc Hsn]. split.
    + apply (lc_tm_succ 0 0 (subst_all sigma n)); exact Hlc.
    + apply SN_succ. exact Hsn.
  - (* T_Rec *)
    specialize (IHn rho env sigma Hrho Henv Hsig HGamma).
    specialize (IHb rho env sigma Hrho Henv Hsig HGamma).
    specialize (IHs rho env sigma Hrho Henv Hsig HGamma).
    simpl.
    pose proof (IsCand_R Ty_Nat rho env Hrho Henv) as HcN.
    destruct HcN as [_ [Nsn _]].
    apply (R_natrec_gen T rho env Hrho Henv (subst_all sigma n)).
    + apply Nsn. exact IHn.
    + exact IHn.
    + exact IHb.
    + exact IHs.
Qed.

Lemma IsCand_nat : IsCand (fun t => locally_closed_tm t /\ strongly_normalizing t).
Proof.
  split.
  - intros t [Hl _]. exact Hl.
  - split.
    * intros t [_ Hs]. exact Hs.
    * split.
      -- intros t t' [Hl Hs] Hstep. split.
         ++ apply lc_tm_step with t; assumption.
         ++ apply SN_step with t; assumption.
      -- split.
         ++ intros t Hnv Hl Hs Hred. split; assumption.
         ++ intros t t' He Hl Hl'. split.
            ** intros [_ Hs]. split.
               --- exact Hl'.
               --- apply (proj1 (erase_sn t t' He Hl Hl')). exact Hs.
            ** intros [_ Hs]. split.
               --- exact Hl.
               --- apply (proj2 (erase_sn t t' He Hl Hl')). exact Hs.
Qed.

Lemma lookup_empty : forall x, lookup_context x empty = None.
Proof. intros x. reflexivity. Qed.

Lemma lookup_empty_absurd : forall x U, lookup_context x empty = Some U -> False.
Proof.
  intros x U H. rewrite lookup_empty in H. discriminate.
Qed.

Lemma subst_all_id : forall t, subst_all (fun x => tm_fvar x) t = t.
Proof.
  induction t as
    [ n | x | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T | | t1 IH1
    | n IHn b IHb s IHs ];
  simpl; try reflexivity; try (f_equal; auto).
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  pose proof
    (fundamental [] empty t T Hty
       (fun _ : atom => (fun t0 : tm => locally_closed_tm t0 /\ strongly_normalizing t0))
       (fun _ : nat => (fun t0 : tm => locally_closed_tm t0 /\ strongly_normalizing t0))
       (fun x : atom => tm_fvar x)
       (fun X => IsCand_nat)
       (fun i => IsCand_nat)
       (fun y => lc_tm_fvar 0 0 y)
       (fun x U H => False_rect _ (lookup_empty_absurd x U H))) as HR.
  rewrite subst_all_id in HR.
  pose proof (IsCand_R T
                (fun _ : atom => (fun t0 : tm => locally_closed_tm t0 /\ strongly_normalizing t0))
                (fun _ : nat => (fun t0 : tm => locally_closed_tm t0 /\ strongly_normalizing t0))
                (fun X => IsCand_nat) (fun i => IsCand_nat)) as Hc.
  destruct Hc as [_ [Hsn _]].
  apply Hsn. exact HR.
Qed.

End SystemFNormalizationRecursionHardTask.
