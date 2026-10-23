(** System F CBV strong-normalization benchmark, Hard variant.
    Features: if. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfHardTask.

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
  | Ty_Bool : ty.

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
  | tm_if : tm -> tm -> tm -> tm.

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

Fixpoint open_ty_rec (k : nat) (U T : ty) : ty :=
  match T with
  | Ty_BVar i => if Nat.eqb k i then U else Ty_BVar i
  | Ty_FVar X => Ty_FVar X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (open_ty_rec k U T1) (open_ty_rec k U T2)
  | Ty_All T1 => Ty_All (open_ty_rec (S k) U T1)
  | Ty_Bool => Ty_Bool
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
  | lc_ty_bool : forall k, lc_ty_at k Ty_Bool.

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
      lc_tm_at K k t1 -> lc_tm_at K k t2 -> lc_tm_at K k t3 -> lc_tm_at K k (tm_if t1 t2 t3).

Definition locally_closed_tm (t : tm) : Prop := lc_tm_at 0 0 t.

Inductive value : tm -> Prop :=
  | v_abs : forall T t,
      locally_closed_tm (tm_abs T t) ->
      value (tm_abs T t)
  | v_tabs : forall t,
      locally_closed_tm (tm_tabs t) ->
      value (tm_tabs t)
  | v_true : value tm_true
  | v_false : value tm_false.

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
  | WF_Bool : forall Delta, wf_ty Delta Ty_Bool.

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
      has_type Delta Gamma (tm_if t1 t2 t3) T.

Inductive multi : tm -> tm -> Prop :=
  | multi_refl : forall x, multi x x
  | multi_step : forall x y z, x --> y -> multi y z -> multi x z.
Notation "t '-->*' u" := (multi t u) (at level 40).

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

(* Construct the logical relation and supporting proofs here. *)

Inductive utm : Type :=
| u_bvar : nat -> utm | u_fvar : atom -> utm
| u_abs : utm -> utm | u_app : utm -> utm -> utm
| u_tabs : utm -> utm | u_tapp : utm -> utm
| u_true : utm | u_false : utm | u_if : utm -> utm -> utm -> utm.

Fixpoint erase (t : tm) : utm :=
  match t with
  | tm_bvar i => u_bvar i | tm_fvar x => u_fvar x
  | tm_abs _ b => u_abs (erase b)
  | tm_app f a => u_app (erase f) (erase a)
  | tm_tabs b => u_tabs (erase b)
  | tm_tapp f _ => u_tapp (erase f)
  | tm_true => u_true | tm_false => u_false
  | tm_if c a b => u_if (erase c) (erase a) (erase b)
  end.

Fixpoint open_u_rec (k : nat) (u t : utm) : utm :=
  match t with
  | u_bvar i => if Nat.eqb k i then u else u_bvar i
  | u_fvar x => u_fvar x
  | u_abs b => u_abs (open_u_rec (S k) u b)
  | u_app f a => u_app (open_u_rec k u f) (open_u_rec k u a)
  | u_tabs b => u_tabs (open_u_rec k u b)
  | u_tapp f => u_tapp (open_u_rec k u f)
  | u_true => u_true | u_false => u_false
  | u_if c a b => u_if (open_u_rec k u c) (open_u_rec k u a) (open_u_rec k u b)
  end.
Definition open_u (t u : utm) := open_u_rec 0 u t.

Fixpoint uinst (sigma : atom -> utm) (t : utm) : utm :=
  match t with
  | u_bvar i => u_bvar i
  | u_fvar x => sigma x
  | u_abs b => u_abs (uinst sigma b)
  | u_app f a => u_app (uinst sigma f) (uinst sigma a)
  | u_tabs b => u_tabs (uinst sigma b)
  | u_tapp f => u_tapp (uinst sigma f)
  | u_true => u_true | u_false => u_false
  | u_if c a b => u_if (uinst sigma c) (uinst sigma a) (uinst sigma b)
  end.
Definition uupdate (sigma : atom -> utm) (x : atom) (u : utm) : atom -> utm :=
  fun y => if Nat.eqb y x then u else sigma y.

Fixpoint ufv (t : utm) : list atom :=
  match t with
  | u_bvar _ | u_true | u_false => []
  | u_fvar x => [x]
  | u_abs b | u_tabs b | u_tapp b => ufv b
  | u_app f a => ufv f ++ ufv a
  | u_if c a b => ufv c ++ ufv a ++ ufv b
  end.

Fixpoint ty_fv (T : ty) : list atom :=
  match T with
  | Ty_BVar _ | Ty_Bool => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fv A ++ ty_fv B
  | Ty_All A => ty_fv A
  end.
Fixpoint ctx_ty_fv (G : context) : list atom :=
  match G with [] => [] | (_,T)::G' => ty_fv T ++ ctx_ty_fv G' end.

Fixpoint max_list (xs : list nat) : nat :=
  match xs with [] => 0 | x::xs' => Nat.max x (max_list xs') end.
Lemma in_le_max : forall xs x, In x xs -> x <= max_list xs.
Proof.
  induction xs as [|a xs IH]; intros x Hin; simpl in *; [contradiction|].
  destruct Hin as [->|Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.
Lemma fresh_notin : forall xs : list nat, exists x, ~ In x xs.
Proof.
  intros xs. exists (S (max_list xs)). intro Hin.
  pose proof (in_le_max xs _ Hin). lia.
Qed.

Lemma uinst_update_fresh : forall t sigma x u,
  ~ In x (ufv t) -> uinst (uupdate sigma x u) t = uinst sigma t.
Proof.
  induction t as [i|a|b IH|f IHf a IHa|b IH|f IH| | |c IHc a IHa d IHd];
    intros sigma x u Hfresh; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. simpl; auto.
    + unfold uupdate. rewrite E. reflexivity.
  - rewrite IH; [reflexivity|exact Hfresh].
  - rewrite IHf, IHa.
    + reflexivity.
    + intro Hin. apply Hfresh. apply in_or_app; right; exact Hin.
    + intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
  - rewrite IH; [reflexivity|exact Hfresh].
  - rewrite IH; [reflexivity|exact Hfresh].
  - reflexivity.
  - reflexivity.
  - rewrite IHc, IHa, IHd.
    + reflexivity.
    + intro Hin. apply Hfresh. apply in_or_app; right; apply in_or_app; right; exact Hin.
    + intro Hin. apply Hfresh. apply in_or_app; right; apply in_or_app; left; exact Hin.
    + intro Hin. apply Hfresh. apply in_or_app; left; exact Hin.
Qed.

Fixpoint subst_u (x : atom) (s t : utm) : utm :=
  match t with
  | u_bvar i => u_bvar i
  | u_fvar y => if Nat.eqb x y then s else u_fvar y
  | u_abs b => u_abs (subst_u x s b)
  | u_app f a => u_app (subst_u x s f) (subst_u x s a)
  | u_tabs b => u_tabs (subst_u x s b)
  | u_tapp f => u_tapp (subst_u x s f)
  | u_true => u_true | u_false => u_false
  | u_if c a b => u_if (subst_u x s c) (subst_u x s a) (subst_u x s b)
  end.

Inductive ulc_at : nat -> utm -> Prop :=
| ulc_bvar : forall k i, i < k -> ulc_at k (u_bvar i)
| ulc_fvar : forall k x, ulc_at k (u_fvar x)
| ulc_abs : forall k b, ulc_at (S k) b -> ulc_at k (u_abs b)
| ulc_app : forall k f a, ulc_at k f -> ulc_at k a -> ulc_at k (u_app f a)
| ulc_tabs : forall k b, ulc_at k b -> ulc_at k (u_tabs b)
| ulc_tapp : forall k f, ulc_at k f -> ulc_at k (u_tapp f)
| ulc_true : forall k, ulc_at k u_true
| ulc_false : forall k, ulc_at k u_false
| ulc_if : forall k c a b, ulc_at k c -> ulc_at k a -> ulc_at k b -> ulc_at k (u_if c a b).
Definition ulc (t : utm) := ulc_at 0 t.
Lemma ulc_weaken : forall k t, ulc_at k t -> ulc_at (S k) t.
Proof. intros k t H; induction H; econstructor; eauto; lia. Qed.

Lemma open_u_lc_identity : forall k t u,
  ulc_at k t -> open_u_rec k u t = t.
Proof.
  intros k t u H; induction H; simpl.
  - destruct (Nat.eqb k i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; assumption.
  - f_equal; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal; assumption.
Qed.

Lemma uinst_open_rec : forall t k u sigma,
  (forall x, ulc (sigma x)) ->
  uinst sigma (open_u_rec k u t) =
  open_u_rec k (uinst sigma u) (uinst sigma t).
Proof.
  induction t as [i|x|b IH|f IHf a IHa|b IH|f IH| | |c IHc a IHa b IHb];
    intros k u sigma Hlc; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - symmetry. apply open_u_lc_identity.
    assert (Hk : forall n, ulc_at n (sigma x)).
    { intro n; induction n; [exact (Hlc x)|eapply ulc_weaken; exact IHn]. }
    exact (Hk k).
  - rewrite (IH (S k) u sigma Hlc). reflexivity.
  - rewrite (IHf k u sigma Hlc), (IHa k u sigma Hlc). reflexivity.
  - rewrite (IH k u sigma Hlc). reflexivity.
  - rewrite (IH k u sigma Hlc). reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (IHc k u sigma Hlc), (IHa k u sigma Hlc), (IHb k u sigma Hlc). reflexivity.
Qed.
Lemma uinst_open : forall t u sigma,
  (forall x, ulc (sigma x)) ->
  uinst sigma (open_u t u) = open_u (uinst sigma t) (uinst sigma u).
Proof. intros; apply uinst_open_rec; assumption. Qed.

Inductive uvalue : utm -> Prop :=
| uv_abs : forall b, ulc (u_abs b) -> uvalue (u_abs b)
| uv_tabs : forall b, ulc (u_tabs b) -> uvalue (u_tabs b)
| uv_true : uvalue u_true | uv_false : uvalue u_false.
Reserved Notation "s '==>' t" (at level 40).
Inductive ustep : utm -> utm -> Prop :=
| US_AppAbs : forall b a, u_app (u_abs b) a ==> open_u b a
| US_App1 : forall f f' a, f ==> f' -> u_app f a ==> u_app f' a
| US_App2 : forall f a a', a ==> a' -> u_app f a ==> u_app f a'
| US_TAppTabs : forall b, u_tapp (u_tabs b) ==> b
| US_TApp : forall f f', f ==> f' -> u_tapp f ==> u_tapp f'
| US_IfTrue : forall a b, u_if u_true a b ==> a
| US_IfFalse : forall a b, u_if u_false a b ==> b
| US_If : forall c c' a b, c ==> c' -> u_if c a b ==> u_if c' a b
where "s '==>' t" := (ustep s t).
Inductive usn : utm -> Prop :=
| USN : forall t, (forall u, t ==> u -> usn u) -> usn t.

Lemma open_u_lc_rec : forall k b u,
  ulc_at (S k) b -> ulc_at k u -> ulc_at k (open_u_rec k u b).
Proof.
  intros k b; revert k.
  induction b as [i|x|b IH|f IHf a IHa|b IH|f IH| | |c IHc a IHa d IHd];
    intros k u Hb Hu; inversion Hb; subst; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + exact Hu.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - constructor. eapply IH; [eassumption|apply ulc_weaken; exact Hu].
  - constructor; [eapply IHf|eapply IHa]; eassumption.
  - constructor. eapply IH; eassumption.
  - constructor. eapply IH; eassumption.
  - constructor.
  - constructor.
  - constructor; [eapply IHc|eapply IHa|eapply IHd]; eassumption.
Qed.
Lemma open_u_lc : forall b u, ulc_at 1 b -> ulc u -> ulc (open_u b u).
Proof. intros; eapply open_u_lc_rec; eauto. Qed.

Lemma ustep_lc : forall t u, t ==> u -> ulc t -> ulc u.
Proof.
  intros t u H; induction H; intros Hlc; inversion Hlc; subst.
  - match goal with Habs : ulc_at 0 (u_abs _) |- _ => inversion Habs; subst end.
    eapply open_u_lc; eassumption.
  - constructor; [eapply IHustep; eassumption|assumption].
  - constructor; [assumption|eapply IHustep; eassumption].
  - match goal with Htabs : ulc_at 0 (u_tabs _) |- _ => inversion Htabs; subst end.
    assumption.
  - constructor. eapply IHustep; eassumption.
  - assumption.
  - assumption.
  - constructor; [eapply IHustep; eassumption|assumption|assumption].
Qed.

Lemma erase_open_tm_rec : forall t k u,
  erase (open_tm_rec k u t) = open_u_rec k (erase u) (erase t).
Proof.
  induction t; intros k u; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; try reflexivity.
  destruct (Nat.eqb k n); reflexivity.
Qed.
Lemma erase_open_tm : forall t u,
  erase (open_tm t u) = open_u (erase t) (erase u).
Proof. intros; apply erase_open_tm_rec. Qed.
Lemma erase_open_tm_ty_rec : forall t k U,
  erase (open_tm_ty_rec k U t) = erase t.
Proof. induction t; intros; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity. Qed.
Lemma erase_tm_ty_subst : forall t X U,
  erase (tm_ty_subst X U t) = erase t.
Proof. induction t; intros; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity. Qed.
Lemma erase_tm_subst : forall t x s,
  erase (tm_subst x s t) = subst_u x (erase s) (erase t).
Proof.
  induction t; intros; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; try reflexivity.
  destruct (Nat.eqb x a); reflexivity.
Qed.

Lemma erase_lc_at : forall K k t,
  lc_tm_at K k t -> ulc_at k (erase t).
Proof.
  intros K k t H; induction H; simpl; try constructor; eauto.
Qed.
Lemma erase_lc : forall t, locally_closed_tm t -> ulc (erase t).
Proof. intros; eapply erase_lc_at; eauto. Qed.

Lemma ulc_at_open_inv_rec : forall k b u,
  ulc_at k u -> ulc_at k (open_u_rec k u b) -> ulc_at (S k) b.
Proof.
  intros k b; revert k; induction b; intros k u Hu Hopen; simpl in Hopen.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor. lia.
    + inversion Hopen; subst. constructor. apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion Hopen; subst. constructor.
    eapply IHb; [eapply ulc_weaken; exact Hu|eassumption].
  - inversion Hopen; subst. apply ulc_app.
    + eapply IHb1; [exact Hu|assumption].
    + eapply IHb2; [exact Hu|assumption].
  - inversion Hopen; subst. apply ulc_tabs. eapply IHb; [exact Hu|assumption].
  - inversion Hopen; subst. apply ulc_tapp. eapply IHb; [exact Hu|assumption].
  - inversion Hopen; constructor.
  - inversion Hopen; constructor.
  - inversion Hopen; subst. apply ulc_if.
    + eapply IHb1; [exact Hu|assumption].
    + eapply IHb2; [exact Hu|assumption].
    + eapply IHb3; [exact Hu|assumption].
Qed.

Lemma ulc_at_open_inv : forall b x,
  ulc (open_u b (u_fvar x)) -> ulc_at 1 b.
Proof. intros; eapply ulc_at_open_inv_rec; [constructor|exact H]. Qed.

Lemma ulc_at_mono : forall i j t, i <= j -> ulc_at i t -> ulc_at j t.
Proof.
  intros i j t Hij H. induction Hij; [exact H|]. eapply ulc_weaken; exact IHHij.
Qed.

Lemma uinst_lc_at : forall t k sigma,
  ulc_at k t -> (forall x, ulc (sigma x)) -> ulc_at k (uinst sigma t).
Proof.
  intros t k sigma H; induction H; intros Hsigma; simpl;
    eauto using ulc_at, ulc_weaken, ulc_at_mono.
  all: eapply ulc_at_mono with (i:=0); [lia|apply Hsigma].
Qed.

Lemma lc_ty_weaken : forall k T, lc_ty_at k T -> lc_ty_at (S k) T.
Proof. intros k T H; induction H; econstructor; eauto; lia. Qed.

Lemma open_ty_lc_inv_rec : forall k T U,
  lc_ty_at k U -> lc_ty_at k (open_ty_rec k U T) -> lc_ty_at (S k) T.
Proof.
  intros k T; revert k; induction T; intros k U HU Hopen; simpl in Hopen.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. apply lc_ty_bvar. lia.
    + inversion Hopen; subst. constructor. apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion Hopen; subst. constructor.
    + eapply IHT1; [exact HU|assumption].
    + eapply IHT2; [exact HU|assumption].
  - inversion Hopen; subst. constructor. eapply IHT; [eapply lc_ty_weaken; exact HU|eassumption].
  - constructor.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H.
  - constructor.
  - constructor; assumption.
  - destruct (fresh_notin L) as [X HX].
    constructor. eapply open_ty_lc_inv_rec with (k:=0) (U:=Ty_FVar X).
    + constructor.
    + apply H0; exact HX.
  - constructor.
Qed.

Lemma erase_step : forall t u, step t u -> erase t ==> erase u.
Proof.
  intros t u H; induction H; simpl.
  - rewrite erase_open_tm. constructor.
  - apply US_App1; exact IHstep.
  - apply US_App2; exact IHstep.
  - unfold open_tm_ty. rewrite erase_open_tm_ty_rec. constructor.
  - apply US_TApp; exact IHstep.
  - apply US_IfTrue.
  - apply US_IfFalse.
  - apply US_If; exact IHstep.
Qed.

Fixpoint ghost_count (t : tm) : nat :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false => 0
  | tm_abs _ b => ghost_count b
  | tm_app f a => ghost_count f + ghost_count a
  | tm_tabs b => S (ghost_count b)
  | tm_tapp f _ => S (ghost_count f)
  | tm_if c a b => ghost_count c + ghost_count a + ghost_count b
  end.
Lemma ghost_open_ty : forall t k U,
  ghost_count (open_tm_ty_rec k U t) = ghost_count t.
Proof. induction t; intros; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; lia. Qed.

Definition uneutral (t : utm) : Prop :=
  match t with u_abs _ | u_tabs _ => False | _ => True end.
Record candidate : Type := Cand {
  cmem : utm -> Prop;
  cand_sn : forall t, cmem t -> usn t;
  cand_step : forall t u, cmem t -> t ==> u -> cmem u;
  cand_neutral : forall t, uneutral t ->
      (forall u, t ==> u -> cmem u) -> cmem t
}.

Definition snmem (t : utm) := usn t.
Lemma sn_candidate : candidate.
Proof.
  refine (Cand snmem _ _ _).
  - auto.
  - intros t u Hsn Hstep. inversion Hsn as [t0 Hall]; subst. exact (Hall u Hstep).
  - intros t Hn Hs. constructor. exact Hs.
Defined.

Definition arrmem (A B : candidate) (t : utm) : Prop :=
  usn t /\ (forall u, cmem A u -> ulc u -> cmem B (u_app t u)).

Lemma arr_neutral_app : forall A B t,
  uneutral t ->
  (forall t', t ==> t' -> arrmem A B t') ->
  forall u, cmem A u -> ulc u -> cmem B (u_app t u).
Proof.
  intros A B t Hneutral Hred.
  assert (Haux : forall u, usn u -> cmem A u -> ulc u -> cmem B (u_app t u)).
  { intros u Hsu. induction Hsu as [u Hsteps IH]; intros Hu Hlu.
    apply (cand_neutral B); [exact I|].
    intros r Hr; inversion Hr; subst.
    - exfalso. simpl in Hneutral. exact Hneutral.
    - match goal with Ht : _ ==> _ |- _ =>
        specialize (Hred _ Ht) as [_ Happly]; apply Happly; [exact Hu|exact Hlu]
      end.
    - match goal with Harg : _ ==> _ |- _ =>
        apply IH; [exact Harg|eapply cand_step; eauto|eapply ustep_lc; eauto]
      end.
  }
  intros u Hu Hlu. apply Haux; [exact (cand_sn A u Hu)|exact Hu|exact Hlu].
Qed.

Lemma arrow_candidate : forall (A B : candidate), candidate.
Proof.
  intros A B. refine (Cand (arrmem A B) _ _ _).
  - intros t [Hsn _]; exact Hsn.
  - intros t u [Hsn Happ] Hstep. split.
    + inversion Hsn as [t0 Hall]; subst. exact (Hall u Hstep).
    + intros a Ha Hla.
      apply (cand_step B (u_app t a) (u_app u a)).
      * apply Happ; assumption.
      * apply US_App1; exact Hstep.
  - intros t Hneutral Hred. split.
    + constructor. intros t' Ht. specialize (Hred t' Ht) as [Hsn _]. exact Hsn.
    + intros u Hu Hlu. eapply arr_neutral_app; eauto.
Defined.

Definition allmem (F : candidate -> candidate) (t : utm) : Prop :=
  usn t /\ forall P, cmem (F P) (u_tapp t).
Lemma all_candidate : forall F : candidate -> candidate, candidate.
Proof.
  intros F. refine (Cand (allmem F) _ _ _).
  - intros t [H _]; exact H.
  - intros t u [Hsn Hall] Hstep. split.
    + inversion Hsn as [t0 Hnext]; subst. exact (Hnext u Hstep).
    + intros P. eapply cand_step.
      * apply Hall.
      * apply US_TApp. exact Hstep.
  - intros t Hneutral Hred. split.
    + constructor. intros u Hu. specialize (Hred u Hu) as [Hsn _]. exact Hsn.
    + intros P. apply (cand_neutral (F P)); [exact I|].
      intros u Hu. inversion Hu; subst.
      * simpl in Hneutral. contradiction.
      * match goal with Ht : t ==> _ |- _ =>
          specialize (Hred _ Ht) as [_ Hall]; exact (Hall P)
        end.
Defined.

Definition tenv := nat -> candidate.
Definition tshift (P : candidate) (theta : tenv) : tenv :=
  fun i => match i with 0 => P | S j => theta j end.
Definition tupdate (theta : tenv) (k : nat) (P : candidate) : tenv :=
  fun i => if Nat.eqb k i then P else theta i.
Definition tempty : tenv := fun _ => sn_candidate.

Fixpoint sem (rho : atom -> candidate) (theta : tenv) (T : ty)
  : candidate :=
  match T with
  | Ty_BVar i => theta i
  | Ty_FVar X => rho X
  | Ty_Arrow A B => arrow_candidate (sem rho theta A) (sem rho theta B)
  | Ty_All B => all_candidate (fun P => sem rho (tshift P theta) B)
  | Ty_Bool => sn_candidate
  end.

Lemma sem_agree : forall d T, lc_ty_at d T ->
  forall rho th1 th2,
    (forall i, i < d -> th1 i = th2 i) ->
  forall t, cmem (sem rho th1 T) t <-> cmem (sem rho th2 T) t.
Proof.
  intros d T Hlc; induction Hlc as [k i Hi|k X|k A B HA IHA HB IHB|k T HT IHT|k];
    intros rho th1 th2 Hag t.
  - cbn [sem]. rewrite Hag by exact Hi. tauto.
  - cbn [sem]. tauto.
  - cbn [sem arrow_candidate arrmem].
    pose proof (IHA rho th1 th2 Hag) as IHA'.
    pose proof (IHB rho th1 th2 Hag) as IHB'.
    split.
    + intros [Hs Happ]. split; [exact Hs|]. intros u Hu Hlu.
      apply (proj1 (IHB' (u_app t u))). apply Happ.
      * apply (proj2 (IHA' u)); exact Hu.
      * exact Hlu.
    + intros [Hs Happ]. split; [exact Hs|]. intros u Hu Hlu.
      apply (proj2 (IHB' (u_app t u))). apply Happ.
      * apply (proj1 (IHA' u)); exact Hu.
      * exact Hlu.
  - cbn [sem all_candidate allmem].
    split.
    + intros [Hs Hall]. split; [exact Hs|]. intros P.
      assert (Hshift : forall i, i < S k -> tshift P th1 i = tshift P th2 i).
      { intros [|i] Hi; simpl; [reflexivity|apply Hag; lia]. }
      apply (proj1 (IHT rho (tshift P th1) (tshift P th2) Hshift (u_tapp t))).
      exact (Hall P).
    + intros [Hs Hall]. split; [exact Hs|]. intros P.
      assert (Hshift : forall i, i < S k -> tshift P th1 i = tshift P th2 i).
      { intros [|i] Hi; simpl; [reflexivity|apply Hag; lia]. }
      apply (proj2 (IHT rho (tshift P th1) (tshift P th2) Hshift (u_tapp t))).
      exact (Hall P).
  - cbn [sem]. tauto.
Qed.

Lemma sem_env_agree : forall T rho th1 th2,
  (forall i t, cmem (th1 i) t <-> cmem (th2 i) t) -> forall t,
  cmem (sem rho th1 T) t <-> cmem (sem rho th2 T) t.
Proof.
  induction T; intros rho th1 th2 Hag t; cbn [sem arrow_candidate arrmem all_candidate allmem].
  - apply Hag.
  - tauto.
  - pose proof (IHT1 rho th1 th2 Hag) as HA.
    pose proof (IHT2 rho th1 th2 Hag) as HB.
    split.
    + intros [Hs Happ]. split; [exact Hs|]. intros u Hu Hlu.
      apply (proj1 (HB (u_app t u))). apply Happ.
      * apply (proj2 (HA u)); exact Hu.
      * exact Hlu.
    + intros [Hs Happ]. split; [exact Hs|]. intros u Hu Hlu.
      apply (proj2 (HB (u_app t u))). apply Happ.
      * apply (proj1 (HA u)); exact Hu.
      * exact Hlu.
  - split.
    + intros [Hs Hall]. split; [exact Hs|]. intros P.
      assert (Hsh : forall i z, cmem (tshift P th1 i) z <-> cmem (tshift P th2 i) z).
      { intros [|i] z; simpl; [tauto|apply Hag]. }
      apply (proj1 (IHT rho (tshift P th1) (tshift P th2) Hsh (u_tapp t))).
      apply Hall.
    + intros [Hs Hall]. split; [exact Hs|]. intros P.
      assert (Hsh : forall i z, cmem (tshift P th1 i) z <-> cmem (tshift P th2 i) z).
      { intros [|i] z; simpl; [tauto|apply Hag]. }
      apply (proj2 (IHT rho (tshift P th1) (tshift P th2) Hsh (u_tapp t))).
      apply Hall.
  - tauto.
Qed.

Lemma tupdate_tshift_agree : forall P theta k Q,
  forall i,
    tshift P (tupdate theta k Q) i =
    tupdate (tshift P theta) (S k) Q i.
Proof.
  intros P theta k Q i. destruct i as [|i]; unfold tupdate; simpl.
  - reflexivity.
  - destruct (Nat.eqb k i); reflexivity.
Qed.

Lemma tupdate_tshift_rel : forall P theta k Q1 Q2,
  (forall t, cmem Q1 t <-> cmem Q2 t) ->
  forall i t,
    cmem (tupdate (tshift P theta) (S k) Q1 i) t <->
    cmem (tshift P (tupdate theta k Q2) i) t.
Proof.
  intros P theta k Q1 Q2 HQ [|i] t; simpl.
  - tauto.
  - unfold tupdate. destruct (Nat.eq_dec k i) as [->|Hneq].
    + rewrite !Nat.eqb_refl. apply HQ.
    + assert (E1 : Nat.eqb k i = false) by (apply Nat.eqb_neq; exact Hneq).
      assert (E2 : Nat.eqb (S k) (S i) = false).
      { apply Nat.eqb_neq. intro E. inversion E. contradiction. }
      rewrite E1, E2. tauto.
Qed.

Lemma sem_open_rec : forall T, forall rho theta k U,
  locally_closed_ty U -> forall t,
  cmem (sem rho theta (open_ty_rec k U T)) t <->
  cmem (sem rho (tupdate theta k (sem rho theta U)) T) t.
Proof.
  induction T; intros rho theta k U HlcU t; cbn [open_ty_rec sem arrow_candidate arrmem all_candidate allmem].
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. unfold tupdate. rewrite Nat.eqb_refl. tauto.
    + unfold tupdate. rewrite E. tauto.
  - tauto.
  - pose proof (IHT1 rho theta k U HlcU) as HA.
    pose proof (IHT2 rho theta k U HlcU) as HB.
    split.
    + intros [Hs Happ]. split; [exact Hs|]. intros u Hu Hlu.
      apply (proj1 (HB (u_app t u))). apply Happ.
      * apply (proj2 (HA u)); exact Hu.
      * exact Hlu.
    + intros [Hs Happ]. split; [exact Hs|]. intros u Hu Hlu.
      apply (proj2 (HB (u_app t u))). apply Happ.
      * apply (proj1 (HA u)); exact Hu.
      * exact Hlu.
  - split.
    + intros [Hs Hall]. split; [exact Hs|]. intros P.
      assert (HU : forall z, cmem (sem rho (tshift P theta) U) z <->
                             cmem (sem rho theta U) z).
      { intros z. apply sem_agree with (d:=0); [assumption|]. intros i Hi; lia. }
      assert (Henv : forall i z,
        cmem (tupdate (tshift P theta) (S k) (sem rho (tshift P theta) U) i) z <->
        cmem (tshift P (tupdate theta k (sem rho theta U)) i) z).
      { intros i z. apply tupdate_tshift_rel. exact HU. }
      apply (proj1 (sem_env_agree T rho
          (tupdate (tshift P theta) (S k) (sem rho (tshift P theta) U))
          (tshift P (tupdate theta k (sem rho theta U))) Henv (u_tapp t))).
      apply (proj1 (IHT rho (tshift P theta) (S k) U HlcU (u_tapp t))).
      apply Hall.
    + intros [Hs Hall]. split; [exact Hs|]. intros P.
      (* symmetric direction *)
      assert (HU : forall z, cmem (sem rho (tshift P theta) U) z <->
                             cmem (sem rho theta U) z).
      { intros z. apply sem_agree with (d:=0); [assumption|]. intros i Hi; lia. }
      assert (Henv : forall i z,
        cmem (tupdate (tshift P theta) (S k) (sem rho (tshift P theta) U) i) z <->
        cmem (tshift P (tupdate theta k (sem rho theta U)) i) z).
      { intros i z. apply tupdate_tshift_rel. exact HU. }
      apply (proj2 (IHT rho (tshift P theta) (S k) U HlcU (u_tapp t))).
      apply (proj2 (sem_env_agree T rho
          (tupdate (tshift P theta) (S k) (sem rho (tshift P theta) U))
          (tshift P (tupdate theta k (sem rho theta U))) Henv (u_tapp t))).
      apply Hall.
  - tauto.
Qed.

Definition rho_update (rho : atom -> candidate) (X : atom) (P : candidate) : atom -> candidate :=
  fun Y => if Nat.eqb Y X then P else rho Y.

Lemma sem_rho_update : forall T, forall X P rho,
  ~ In X (ty_fv T) -> forall theta t,
  cmem (sem rho theta T) t <-> cmem (sem (rho_update rho X P) theta T) t.
Proof.
  induction T; intros X P rho Hfresh theta t; cbn [sem arrow_candidate arrmem all_candidate allmem] in *.
  - tauto.
  - simpl in Hfresh. destruct (Nat.eqb a X) eqn:E.
    + apply Nat.eqb_eq in E; subst. exfalso. apply Hfresh. simpl; auto.
    + unfold rho_update. rewrite E. tauto.
  - pose proof (IHT1 X P rho) as HA.
    pose proof (IHT2 X P rho) as HB.
    assert (Hf1 : ~ In X (ty_fv T1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hf2 : ~ In X (ty_fv T2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    specialize (HA Hf1 theta); specialize (HB Hf2 theta).
    split.
    + intros [Hs Happ]. split; [exact Hs|]. intros u Hu Hlu.
      apply (proj1 (HB (u_app t u))). apply Happ; [apply (proj2 (HA u)); exact Hu|exact Hlu].
    + intros [Hs Happ]. split; [exact Hs|]. intros u Hu Hlu.
      apply (proj2 (HB (u_app t u))). apply Happ; [apply (proj1 (HA u)); exact Hu|exact Hlu].
  - pose proof (IHT X P rho) as Hbody.
    specialize (Hbody Hfresh).
    split.
    + intros [Hs Hall]. split; [exact Hs|]. intros Q.
      apply (proj1 (Hbody (tshift Q theta) (u_tapp t))). apply Hall.
    + intros [Hs Hall]. split; [exact Hs|]. intros Q.
      apply (proj2 (Hbody (tshift Q theta) (u_tapp t))). apply Hall.
  - tauto.
Qed.

Definition term_env_ok (rho : atom -> candidate) (Gamma : context)
  (sigma : atom -> utm) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> cmem (sem rho tempty T) (sigma x).
Definition term_env_lc (sigma : atom -> utm) : Prop := forall x, ulc (sigma x).

Lemma lookup_tyfv_in_ctx : forall Gamma x T,
  lookup_context x Gamma = Some T -> forall Y,
  In Y (ty_fv T) -> In Y (ctx_ty_fv Gamma).
Proof.
  induction Gamma as [|[z U] G IH]; intros x T Hlook Y HY; simpl in Hlook; try discriminate.
  simpl. destruct (Nat.eqb x z) eqn:E.
  - inversion Hlook; subst. apply in_or_app; left; exact HY.
  - apply in_or_app; right. eapply IH; eauto.
Qed.

Lemma term_env_ok_update : forall rho G sigma x A u,
  term_env_ok rho G sigma -> cmem (sem rho tempty A) u ->
  term_env_ok rho (update G x A) (uupdate sigma x u).
Proof.
  intros rho G sigma x A u Henv Hu y T Hlook.
  unfold update in Hlook. simpl in Hlook.
  destruct (Nat.eqb y x) eqn:E.
  - inversion Hlook; subst. unfold uupdate. rewrite E. exact Hu.
  - unfold uupdate. rewrite E. eapply Henv; eassumption.
Qed.

Lemma term_env_lc_update : forall sigma x u,
  term_env_lc sigma -> ulc u -> term_env_lc (uupdate sigma x u).
Proof.
  intros sigma x u Henv Hu y. unfold uupdate. destruct (Nat.eqb y x); auto.
Qed.

Lemma term_env_ok_rho_update : forall rho G sigma X P,
  term_env_ok rho G sigma -> ~ In X (ctx_ty_fv G) ->
  term_env_ok (rho_update rho X P) G sigma.
Proof.
  intros rho G sigma X P Henv Hfresh x T Hlook.
  pose proof (lookup_tyfv_in_ctx G x T Hlook) as Hsupport.
  assert (Hft : ~ In X (ty_fv T)).
  { intro Hin. apply Hfresh. eapply Hsupport; eauto. }
  apply (proj1 (sem_rho_update T X P rho Hft tempty (sigma x))).
  eapply Henv; eassumption.
Qed.

Lemma usn_no_step : forall t, (forall u, ~ t ==> u) -> usn t.
Proof. intros t H; constructor; intros u Hu; exfalso; exact (H u Hu). Qed.

Lemma beta_expand : forall A B b,
  (forall u, cmem A u -> ulc u -> cmem B (open_u b u)) ->
  forall u, cmem A u -> ulc u -> cmem B (u_app (u_abs b) u).
Proof.
  intros A B b Hbody u Hu Hlu.
  assert (Haux : forall u, usn u -> cmem A u -> ulc u -> cmem B (u_app (u_abs b) u)).
  { intros v Hsn. induction Hsn as [v Hsteps IH]; intros Hv Hlv.
    apply (cand_neutral B); [exact I|].
    intros r Hr; inversion Hr; subst.
    - apply Hbody; assumption.
    - match goal with Habs : u_abs _ ==> _ |- _ => inversion Habs end.
    - match goal with Harg : v ==> _ |- _ =>
        apply IH; [exact Harg|eapply cand_step; eauto|eapply ustep_lc; eauto]
      end.
  }
  apply Haux; [exact (cand_sn A u Hu)|exact Hu|exact Hlu].
Qed.

Lemma if_compat : forall C c a b,
  cmem sn_candidate c -> cmem C a -> cmem C b -> cmem C (u_if c a b).
Proof.
  intros C c a b Hc. revert a b.
  induction Hc as [c Hsteps IH]; intros a b Ha Hb.
  apply (cand_neutral C); [exact I|].
  intros r Hr; inversion Hr; subst.
  - exact Ha.
  - exact Hb.
  - apply IH; assumption.
Qed.

Lemma erase_sn_lift : forall e, usn e -> forall t, erase t = e -> strongly_normalizing t.
Proof.
  intros e Hsn; induction Hsn as [e Hnext IH]; intros t Er.
  constructor; intros u Hu.
  eapply IH with (u:=erase u).
  - rewrite <- Er. apply erase_step. exact Hu.
  - reflexivity.
Qed.

Lemma sn_of_no_step : forall t,
  (forall u, ~ step t u) -> strongly_normalizing t.
Proof. intros t H; constructor; intros u Hu; exfalso; exact (H u Hu). Qed.

Lemma sn_from_successors : forall t,
  (forall u, step t u -> strongly_normalizing u) -> strongly_normalizing t.
Proof. intros; constructor; auto. Qed.

Lemma sn_if : forall c t e,
  strongly_normalizing c -> strongly_normalizing t -> strongly_normalizing e ->
  locally_closed_tm t -> locally_closed_tm e ->
  strongly_normalizing (tm_if c t e).
Proof.
  intros c t e Hc; revert t e.
  induction Hc as [c Hstep IH]; intros t e Ht He Hlt Hle.
  constructor; intros u Hu; inversion Hu; subst.
  - exact Ht.
  - exact He.
  - eapply IH; eauto.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T -> forall rho sigma,
  term_env_ok rho Gamma sigma -> term_env_lc sigma ->
  cmem (sem rho tempty T) (uinst sigma (erase t)) /\
  ulc (uinst sigma (erase t)).
Proof.
  intros Delta Gamma t T HT. induction HT; intros rho sigma Henv Hsigma.
  - split; [eapply Henv; eassumption|]. simpl. apply Hsigma.
  - unfold cmem. cbn [sem arrow_candidate arrmem erase uinst]. split.
    + split.
      * apply usn_no_step. intros u Hstep. inversion Hstep.
      * intros u Hu Hlu.
      assert (Hbody : forall v, cmem (sem rho tempty T1) v -> ulc v ->
          cmem (sem rho tempty T2) (open_u (uinst sigma (erase t2)) v)).
      { intros v Hv Hlv. destruct (fresh_notin (L ++ ufv (erase t2))) as [x Hx].
        assert (HxL : ~ In x L) by (intro Hin; apply Hx; apply in_or_app; left; exact Hin).
        assert (HxB : ~ In x (ufv (erase t2))) by
          (intro Hin; apply Hx; apply in_or_app; right; exact Hin).
        assert (Henv' : term_env_ok rho (update Gamma x T1) (uupdate sigma x v)).
        { eapply term_env_ok_update; eauto. }
        assert (Hsigma' : term_env_lc (uupdate sigma x v)).
        { eapply term_env_lc_update; eauto. }
        pose proof (H1 x HxL rho (uupdate sigma x v) Henv' Hsigma') as Hfund.
        assert (Eopen : uinst (uupdate sigma x v) (erase (open_tm t2 (tm_fvar x))) =
          open_u (uinst sigma (erase t2)) v).
        { rewrite erase_open_tm. rewrite uinst_open by exact Hsigma'.
          rewrite uinst_update_fresh by exact HxB.
          simpl. unfold uupdate. rewrite Nat.eqb_refl. reflexivity. }
        rewrite Eopen in Hfund. destruct Hfund as [Hr _]. exact Hr. }
      eapply beta_expand; [exact Hbody|exact Hu|exact Hlu].
    + simpl. apply ulc_abs.
      destruct (fresh_notin (L ++ ufv (erase t2))) as [x Hx].
      assert (HxL : ~ In x L) by (intro Hin; apply Hx; apply in_or_app; left; exact Hin).
      assert (HxB : ~ In x (ufv (erase t2))) by
        (intro Hin; apply Hx; apply in_or_app; right; exact Hin).
      assert (Hvar : cmem (sem rho tempty T1) (u_fvar x)).
      { apply (cand_neutral (sem rho tempty T1)); [exact I|].
        intros y Hy; inversion Hy. }
      assert (Henv' : term_env_ok rho (update Gamma x T1) (uupdate sigma x (u_fvar x))).
      { eapply term_env_ok_update; eauto. }
      assert (Hsigma' : term_env_lc (uupdate sigma x (u_fvar x))).
      { eapply term_env_lc_update; [exact Hsigma|constructor]. }
      pose proof (H1 x HxL rho (uupdate sigma x (u_fvar x)) Henv' Hsigma') as Hfund.
      assert (Eopen : uinst (uupdate sigma x (u_fvar x)) (erase (open_tm t2 (tm_fvar x))) =
          open_u (uinst sigma (erase t2)) (u_fvar x)).
      { rewrite erase_open_tm. rewrite uinst_open by exact Hsigma'.
        rewrite uinst_update_fresh by exact HxB.
        simpl. unfold uupdate. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Eopen in Hfund. destruct Hfund as [_ Hl].
      apply ulc_at_open_inv with (x:=x). exact Hl.
  - pose proof (IHHT1 rho sigma Henv Hsigma) as HF.
    pose proof (IHHT2 rho sigma Henv Hsigma) as HA.
    destruct HF as [Hf Hlf]. destruct HA as [Ha Hla].
    split.
    + cbn [sem arrow_candidate arrmem] in Hf. apply Hf; assumption.
    + simpl. constructor; assumption.
  - unfold cmem. cbn [sem all_candidate allmem erase uinst]. split.
    + split.
      * apply usn_no_step. intros u Hstep. inversion Hstep.
      * intros P.
        apply (cand_neutral (sem rho (tshift P tempty) T)); [exact I|].
        intros r Hred. inversion Hred; subst;
          try match goal with Hbad : u_tabs _ ==> _ |- _ => inversion Hbad end.
        destruct (fresh_notin (L ++ ty_fv T ++ ctx_ty_fv Gamma)) as [X HX].
      assert (HXL : ~ In X L).
      { intro Hin; apply HX. apply in_or_app; left; exact Hin. }
      assert (HXT : ~ In X (ty_fv T)).
      { intro Hin; apply HX. apply in_or_app; right. apply in_or_app; left; exact Hin. }
      assert (HXG : ~ In X (ctx_ty_fv Gamma)).
      { intro Hin; apply HX. apply in_or_app; right. apply in_or_app; right; exact Hin. }
      set (rho' := rho_update rho X P).
      specialize (H0 X HXL rho' sigma).
      assert (Henv' : term_env_ok rho' Gamma sigma).
      { unfold rho'. eapply term_env_ok_rho_update; eauto. }
      specialize (H0 Henv' Hsigma) as [Hr Hl].
      unfold rho' in Hr.
      unfold open_tm_ty in Hr. rewrite erase_open_tm_ty_rec in Hr.
      assert (HU : locally_closed_ty (Ty_FVar X)) by constructor.
      pose proof (sem_open_rec T rho' tempty 0 (Ty_FVar X) HU
                    (uinst sigma (erase t))) as Hopen.
      assert (Psem : sem rho' tempty (Ty_FVar X) = P).
      { unfold rho', sem, rho_update. simpl. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Psem in Hopen.
      assert (Hshift : forall i z,
        cmem (tupdate tempty 0 P i) z <-> cmem (tshift P tempty i) z).
      { intros [|i] z; simpl; [unfold tupdate; simpl; tauto|tauto]. }
      apply (proj2 (sem_rho_update T X P rho HXT (tshift P tempty)
        (uinst sigma (erase t)))).
      apply (proj1 (sem_env_agree T rho'
        (tupdate tempty 0 P) (tshift P tempty) Hshift
        (uinst sigma (erase t)))).
      apply (proj1 Hopen). exact Hr.
    + simpl. constructor.
      destruct (fresh_notin (L ++ ctx_ty_fv Gamma)) as [X HX].
      assert (HXL : ~ In X L) by (intro Hin; apply HX; apply in_or_app; left; exact Hin).
      assert (HXG : ~ In X (ctx_ty_fv Gamma)) by
        (intro Hin; apply HX; apply in_or_app; right; exact Hin).
      set (rho' := rho_update rho X sn_candidate).
      assert (Henv' : term_env_ok rho' Gamma sigma).
      { unfold rho'. eapply term_env_ok_rho_update; eauto. }
      pose proof (H0 X HXL rho' sigma Henv' Hsigma) as Hfund.
      destruct Hfund as [_ Hl]. unfold open_tm_ty in Hl.
      rewrite erase_open_tm_ty_rec in Hl. exact Hl.
  - pose proof (IHHT rho sigma Henv Hsigma) as HF.
    destruct HF as [Hf Hlf].
    assert (HU : locally_closed_ty U) by (eapply wf_ty_lc; eassumption).
    pose proof (sem_open_rec T rho tempty 0 U HU
                  (u_tapp (uinst sigma (erase t)))) as Hopen.
    set (P := sem rho tempty U).
    assert (Hshift : forall i z,
      cmem (tupdate tempty 0 P i) z <-> cmem (tshift P tempty i) z).
    { intros [|i] z; simpl; [unfold tupdate; simpl; tauto|tauto]. }
    split.
    + apply (proj2 Hopen).
      apply (proj2 (sem_env_agree T rho (tupdate tempty 0 P)
        (tshift P tempty) Hshift (u_tapp (uinst sigma (erase t))))).
      cbn [sem all_candidate allmem] in Hf. apply Hf.
    + simpl. constructor. exact Hlf.
  - split; [apply (cand_neutral sn_candidate); [exact I|intros u Hu; inversion Hu]|constructor].
  - split; [apply (cand_neutral sn_candidate); [exact I|intros u Hu; inversion Hu]|constructor].
  - pose proof (IHHT1 rho sigma Henv Hsigma) as HC.
    pose proof (IHHT2 rho sigma Henv Hsigma) as HA.
    pose proof (IHHT3 rho sigma Henv Hsigma) as HB.
    destruct HC as [Hc Hlc]. destruct HA as [Ha Hla]. destruct HB as [Hb Hlb].
    split.
    + eapply if_compat; eassumption.
    + simpl. constructor; assumption.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T HT.
  assert (Henv : term_env_ok (fun _ => sn_candidate) empty (fun x => u_fvar x)).
  { intros x U Hlook. discriminate. }
  assert (Hsigma : term_env_lc (fun x => u_fvar x)).
  { intros x. constructor. }
  pose proof (fundamental [] empty t T HT (fun _ => sn_candidate)
    (fun x => u_fvar x) Henv Hsigma) as [Hrel Hlc].
  assert (Hid : uinst (fun x => u_fvar x) (erase t) = erase t).
  { generalize (erase t) as e. intro e. induction e; simpl;
      try rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; reflexivity. }
  rewrite Hid in Hrel.
  eapply erase_sn_lift; [eapply cand_sn; exact Hrel|reflexivity].
Qed.

End SystemFNormalizationIfHardTask.
