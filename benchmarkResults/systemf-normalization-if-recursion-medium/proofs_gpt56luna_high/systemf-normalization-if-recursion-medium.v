(** System F CBV strong-normalization benchmark, Medium variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfRecursionMediumTask.

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

Inductive strongly_normalizing : tm -> Prop :=
  | SN_intro : forall t,
      (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.

Hint Constructors lc_ty_at lc_tm_at value : core.

Lemma lc_ty_open_inv : forall k T X,
    lc_ty_at k (open_ty_rec k (Ty_FVar X) T) ->
    lc_ty_at (S k) T.
Proof.
  intros k T X. revert k X. induction T as [i|Y|T1 IH1 T2 IH2|T IH| |];
    intros k X H;
    simpl in H.
  - destruct (Nat.eqb_spec k i) as [E|E].
    + subst i. constructor. lia.
    + inversion H. constructor. lia.
  - inversion H. constructor.
  - inversion H. constructor; eauto.
  - inversion H. constructor. eauto.
  - constructor.
  - constructor.
Qed.

Lemma numeric_sn : forall n, numeric_value n -> strongly_normalizing n.
Proof.
  intros n H. induction H.
  - constructor. intros u Hu. inversion Hu.
  - constructor. intros u Hu. inversion Hu. eauto.
Qed.

Lemma value_sn : forall v, value v -> strongly_normalizing v.
Proof.
  intros v H. induction H.
  - constructor. intros u Hu. inversion Hu.
  - constructor. intros u Hu. inversion Hu.
  - constructor. intros u Hu. inversion Hu.
  - constructor. intros u Hu. inversion Hu.
  - apply numeric_sn. assumption.
Qed.

Lemma expression_lifting_step : forall R t t',
    expression_lifting R t -> t --> t' -> expression_lifting R t'.
Proof.
  intros R t t' [Hlc [Hsn Hend]] Hstep. repeat split.
  - apply lc_step with t; assumption.
  - apply Hsn with t; assumption.
  - intros v Hmulti Hv. apply Hend with (v := v).
    + apply multi_step with t'; assumption.
    + assumption.
Qed.

Lemma expression_lifting_multi : forall R t t',
    expression_lifting R t -> t -->* t' -> expression_lifting R t'.
Proof.
  intros R t t' H Hm. induction Hm.
  - exact H.
  - apply IHHm. apply expression_lifting_step with x; assumption.
Qed.

Lemma sn_app_aux : forall R1 R2 t1,
    strongly_normalizing t1 ->
    expression_lifting R1 t1 ->
    (forall v, R1 v -> exists U body,
      v = tm_abs U body /\ forall arg, R2 arg ->
        expression_lifting R2 (open_tm body arg)) ->
    forall t2, expression_lifting R2 t2 ->
    strongly_normalizing (tm_app t1 t2).
Proof.
  intros R1 R2 t1 Hsn1 Hfun Hshape.
  induction Hsn1 as [t1 Hred1 IH1].
  intros t2 Hsn2. destruct Hsn2 as [Hlc2 [Hsn2 Hend2]].
  induction Hsn2 as [t2 Hred2 IH2].
  constructor. intros u Hu. inversion Hu; subst.
  - destruct (Hshape t1) as [U [body [Heq Hb]]].
    + apply Hend1 with (v := t1); [constructor|assumption].
    + apply Hb. assumption. exact Hlc2.
  - apply IH1.
    + apply expression_lifting_step with t1; assumption.
    + apply Hshape.
  - apply IH2. assumption.
  - apply Hb.
Qed.
Lemma lc_tm_open_inv : forall K k t x,
    lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
    lc_tm_at K (S k) t.
Proof.
  intros K k t x. revert K k x. induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |t1 IH1 t2 IH2 t3 IH3| |t IH|n IHn b IHb s IHs];
    intros K k x H; simpl in H.
  - destruct (Nat.eqb_spec k i) as [E|E].
    + subst i. constructor. lia.
    + inversion H. constructor. lia.
  - inversion H. constructor.
  - inversion H. constructor.
    + assumption.
    + apply (IH K (S k) x). assumption.
  - inversion H. constructor.
    + apply (IH1 K k x). assumption.
    + apply (IH2 K k x). assumption.
  - inversion H. constructor. apply (IH (S K) k x). assumption.
  - inversion H. constructor.
    + apply (IH K k x). assumption.
    + assumption.
  - constructor.
  - constructor.
  - inversion H. constructor.
    + apply (IH1 K k x). assumption.
    + apply (IH2 K k x). assumption.
    + apply (IH3 K k x). assumption.
  - constructor.
  - inversion H. constructor. apply (IH K k x). assumption.
  - inversion H. constructor.
    + apply (IHn K k x). assumption.
    + apply (IHb K k x). assumption.
    + apply (IHs K k x). assumption.
Qed.

Lemma lc_tm_ty_open_inv : forall K k t X,
    lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
    lc_tm_at (S K) k t.
Proof.
  intros K k t X. revert K k X. induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |t1 IH1 t2 IH2 t3 IH3| |t IH|n IHn b IHb s IHs];
    intros K k X H; simpl in H.
  - inversion H. constructor; assumption.
  - inversion H. constructor.
  - inversion H. constructor.
    + apply (lc_ty_open_inv K T X). assumption.
    + apply (IH K (S k) X). assumption.
  - inversion H. constructor.
    + apply (IH1 K k X). assumption.
    + apply (IH2 K k X). assumption.
  - inversion H. constructor. apply (IH (S K) k X). assumption.
  - inversion H. constructor.
    + apply (IH K k X). assumption.
    + eapply lc_ty_open_inv; eassumption.
  - constructor.
  - constructor.
  - inversion H. constructor.
    + apply (IH1 K k X). assumption.
    + apply (IH2 K k X). assumption.
    + apply (IH3 K k X). assumption.
  - constructor.
  - inversion H. constructor. apply (IH K k X). assumption.
  - inversion H. constructor.
    + apply (IHn K k X). assumption.
    + apply (IHb K k X). assumption.
    + apply (IHs K k X). assumption.
Qed.

Fixpoint list_max (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (list_max L')
  end.

Lemma list_max_bound : forall L x, In x L -> x <= list_max L.
Proof.
  induction L as [|y L IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [->|H].
    + apply Nat.le_max_l.
    + etransitivity; [apply IH; assumption|apply Nat.le_max_r].
Qed.

Lemma exists_fresh : forall L : list atom, exists x, ~ In x L.
Proof.
  intro L. exists (S (list_max L)). intro H.
  pose proof (list_max_bound L (S (list_max L)) H). lia.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H. induction H.
  - constructor.
  - constructor; assumption.
  - destruct (exists_fresh L) as [X HX].
    constructor. apply lc_ty_open_inv with (X := X). apply H0; assumption.
  - constructor.
  - constructor.
Qed.

Lemma typing_lc : forall Delta Gamma t T,
    has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T Ht.
  induction Ht.
  - constructor.
  - destruct (exists_fresh L) as [x Hx].
    constructor.
    + apply (wf_ty_lc Delta T1). assumption.
    + apply lc_tm_open_inv with (x := x). apply H1; assumption.
  - constructor; assumption.
  - destruct (exists_fresh L) as [X HX].
    constructor. apply lc_tm_ty_open_inv with (X := X). apply H0; assumption.
  - constructor.
    + assumption.
    + apply (wf_ty_lc Delta U). assumption.
  - constructor.
  - constructor.
  - constructor.
    + assumption.
    + assumption.
    + assumption.
  - constructor.
  - constructor. assumption.
  - constructor.
    + assumption.
    + assumption.
    + assumption.
Qed.

Lemma lc_tm_weak : forall K k t,
    lc_tm_at K k t -> lc_tm_at K (S k) t.
Proof.
  intros K k t H. induction H.
  - constructor. lia.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma lc_ty_weak : forall K T,
    lc_ty_at K T -> lc_ty_at (S K) T.
Proof.
  intros K T H. induction H.
  - constructor. lia.
  - constructor.
  - constructor; assumption.
  - constructor. assumption.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_type_weak : forall K k t,
    lc_tm_at K k t -> lc_tm_at (S K) k t.
Proof.
  intros K k t H. induction H.
  - constructor. lia.
  - constructor.
  - constructor.
    + apply lc_ty_weak. assumption.
    + assumption.
  - constructor.
    + assumption.
    + assumption.
  - constructor; assumption.
  - constructor.
    + assumption.
    + apply lc_ty_weak. assumption.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma lc_ty_open : forall k T U,
    lc_ty_at (S k) T -> lc_ty_at k U ->
    lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k T U. revert k U.
  induction T as [i|X|T1 IH1 T2 IH2|T IH| |];
    intros k U Ht HU; simpl in *.
  - inversion Ht. destruct (Nat.eqb_spec k i) as [E|E].
    + subst i. exact HU.
    + constructor. lia.
  - constructor.
  - inversion Ht. constructor; eauto.
  - inversion Ht. constructor. apply (IH (S k) U).
    + assumption.
    + apply lc_ty_weak. assumption.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_open : forall K k t u,
    lc_tm_at K (S k) t -> lc_tm_at K k u ->
    lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t u. revert K k u.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |t1 IH1 t2 IH2 t3 IH3| |t IH|n IHn b IHb s IHs];
    intros K k u Ht Hu; simpl in *.
  - inversion Ht. destruct (Nat.eqb_spec k i) as [E|E].
    + subst i. exact Hu.
    + constructor. lia.
  - constructor.
  - inversion Ht. constructor.
    + assumption.
    + apply (IH K (S k) u).
      * assumption.
      * apply lc_tm_weak. assumption.
  - inversion Ht. constructor.
    + apply (IH1 K k u); assumption.
    + apply (IH2 K k u); assumption.
  - inversion Ht. constructor. apply (IH (S K) k u).
    + assumption.
    + apply lc_tm_type_weak. assumption.
  - inversion Ht. constructor.
    + apply (IH K k u); assumption.
    + assumption.
  - constructor.
  - constructor.
  - inversion Ht. constructor.
    + apply (IH1 K k u); assumption.
    + apply (IH2 K k u); assumption.
    + apply (IH3 K k u); assumption.
  - constructor.
  - inversion Ht. constructor. apply (IH K k u); assumption.
  - inversion Ht. constructor.
    + apply (IHn K k u); assumption.
    + apply (IHb K k u); assumption.
    + apply (IHs K k u); assumption.
Qed.

Lemma lc_tm_ty_open : forall K k t U,
    lc_tm_at (S K) k t -> lc_ty_at K U ->
    lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t U. revert K k U.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |t1 IH1 t2 IH2 t3 IH3| |t IH|n IHn b IHb s IHs];
    intros K k U Ht HU; simpl in *.
  - inversion Ht. constructor. assumption.
  - constructor.
  - inversion Ht. constructor.
    + apply lc_ty_open; assumption.
    + apply (IH K (S k) U).
      * assumption.
      * assumption.
  - inversion Ht. constructor.
    + apply (IH1 K k U); assumption.
    + apply (IH2 K k U); assumption.
  - inversion Ht. constructor. apply (IH (S K) k U).
    + assumption.
    + apply lc_ty_weak. assumption.
  - inversion Ht. constructor.
    + apply (IH K k U).
      * assumption.
      * assumption.
    + eapply lc_ty_open.
      * assumption.
      * assumption.
  - constructor.
  - constructor.
  - inversion Ht. constructor.
    + apply (IH1 K k U); assumption.
    + apply (IH2 K k U); assumption.
    + apply (IH3 K k U); assumption.
  - constructor.
  - inversion Ht. constructor. apply (IH K k U); assumption.
  - inversion Ht. constructor.
    + apply (IHn K k U); assumption.
    + apply (IHb K k U); assumption.
    + apply (IHs K k U); assumption.
Qed.

Lemma numeric_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H. induction H; constructor; assumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H. induction H.
  - assumption.
  - assumption.
  - constructor.
  - constructor.
  - apply numeric_lc. assumption.
Qed.

Lemma lc_step : forall t u, locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Ht Hs. induction Hs; simpl in *; inversion Ht; subst; simpl in *.
  - apply lc_tm_open.
    + inversion H; assumption.
    + apply value_lc. assumption.
  - constructor.
    + apply IHHs. assumption.
    + assumption.
  - constructor.
    + assumption.
    + apply IHHs. assumption.
  - apply lc_tm_ty_open.
    + inversion H; assumption.
    + assumption.
  - constructor.
    + apply IHHs. assumption.
    + assumption.
  - constructor. apply IHHs. assumption.
  - constructor.
    + apply IHHs. assumption.
    + assumption.
    + assumption.
  - constructor.
    + assumption.
    + apply IHHs. assumption.
    + assumption.
  - constructor.
    + apply numeric_lc. assumption.
    + apply value_lc. assumption.
    + apply IHHs. assumption.
  - assumption.
  - constructor.
    + constructor.
      * assumption.
      * apply numeric_lc. assumption.
    + constructor.
      * inversion H7; assumption.
      * assumption.
      * assumption.
  - assumption.
  - assumption.
  - constructor.
    + apply IHHs. assumption.
    + assumption.
    + assumption.
Qed.

Definition type_substitution := atom -> ty.

Definition term_substitution := atom -> tm.

Fixpoint instantiate_ty (theta : type_substitution) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow T1 T2 =>
      Ty_Arrow (instantiate_ty theta T1) (instantiate_ty theta T2)
  | Ty_All T1 => Ty_All (instantiate_ty theta T1)
  | Ty_Bool => Ty_Bool
  | Ty_Nat => Ty_Nat
  end.

Fixpoint instantiate
    (theta : type_substitution) (gamma : term_substitution) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => gamma x
  | tm_abs T t1 => tm_abs (instantiate_ty theta T) (instantiate theta gamma t1)
  | tm_app t1 t2 => tm_app (instantiate theta gamma t1) (instantiate theta gamma t2)
  | tm_tabs t1 => tm_tabs (instantiate theta gamma t1)
  | tm_tapp t1 T => tm_tapp (instantiate theta gamma t1) (instantiate_ty theta T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t1 t2 t3 => tm_if (instantiate theta gamma t1) (instantiate theta gamma t2) (instantiate theta gamma t3)
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (instantiate theta gamma t)
  | tm_natrec n b s => tm_natrec (instantiate theta gamma n) (instantiate theta gamma b) (instantiate theta gamma s)
  end.

Definition type_substitution_closed (theta : type_substitution) : Prop :=
  forall X : atom, locally_closed_ty (theta X).

Definition term_substitution_closed (gamma : term_substitution) : Prop :=
  forall x : atom, locally_closed_tm (gamma x).

Definition relation := tm -> Prop.
Record value_candidate := {
  candidate_relation : relation;
  candidate_values : forall v, candidate_relation v -> value v
}.
Definition relation_env := atom -> option value_candidate.
Definition relation_update (rho : relation_env) (X : atom) (a : value_candidate) :=
  fun Y => if Nat.eqb X Y then Some a else rho Y.

Definition expression_lifting (R : relation) (t : tm) : Prop :=
  locally_closed_tm t /\ strongly_normalizing t /\
  forall v, t -->* v -> value v -> R v.

Fixpoint value_relation (eta : list value_candidate) (rho : relation_env)
    (T : ty) (v : tm) : Prop :=
  match T with
  | Ty_BVar i =>
      match nth_error eta i with Some a => a.(candidate_relation) v | None => False end
  | Ty_FVar X =>
      match rho X with Some a => a.(candidate_relation) v | None => False end
  | Ty_Arrow T1 T2 =>
      value v /\ exists U body, v = tm_abs U body /\
      forall arg, value_relation eta rho T1 arg ->
        expression_lifting (value_relation eta rho T2) (open_tm body arg)
  | Ty_All T =>
      value v /\ exists body, v = tm_tabs body /\
      forall (U : ty) (a : value_candidate), locally_closed_ty U ->
        expression_lifting (value_relation (a :: eta) rho T) (open_tm_ty body U)
  | Ty_Bool => value v /\ (v = tm_true \/ v = tm_false)
  | Ty_Nat => value v /\ numeric_value v
  end.

Definition expression_relation eta rho T t :=
  expression_lifting (value_relation eta rho T) t.

Definition related_substitution (rho : relation_env) (Gamma : context)
    (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation [] rho T (gamma x).

Fixpoint ty_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_atoms T1 ++ ty_atoms T2
  | Ty_All T1 => ty_atoms T1
  | Ty_Bool => []
  | Ty_Nat => []
  end.

Fixpoint tm_ty_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false | tm_zero => []
  | tm_abs T t1 => ty_atoms T ++ tm_ty_atoms t1
  | tm_app t1 t2 => tm_ty_atoms t1 ++ tm_ty_atoms t2
  | tm_tabs t1 => tm_ty_atoms t1
  | tm_tapp t1 T => tm_ty_atoms t1 ++ ty_atoms T
  | tm_if t1 t2 t3 => tm_ty_atoms t1 ++ tm_ty_atoms t2 ++ tm_ty_atoms t3
  | tm_succ t1 => tm_ty_atoms t1
  | tm_natrec n b s => tm_ty_atoms n ++ tm_ty_atoms b ++ tm_ty_atoms s
  end.

Fixpoint context_atoms (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: Gamma' => ty_atoms T ++ context_atoms Gamma'
  end.

Definition related_at (eta : list value_candidate) (rho : relation_env)
    (Gamma : context) (gamma : term_substitution) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> value_relation eta rho T (gamma x).

Lemma expression_lifting_mono : forall R R' t,
    (forall v, R v -> R' v) -> expression_lifting R t ->
    expression_lifting R' t.
Proof.
  intros R R' t Hmono H. destruct H as [Hlc [Hsn Hend]].
  split; [exact Hlc|]. split; [exact Hsn|].
  intros v Hmulti Hv. apply Hmono. apply Hend; assumption.
Qed.

Lemma expression_lifting_iff : forall R R' t,
    (forall v, R v <-> R' v) ->
    expression_lifting R t <-> expression_lifting R' t.
Proof.
  intros R R' t H. split.
  - apply (expression_lifting_mono R R' t); intros; apply (proj1 (H _)); assumption.
  - apply (expression_lifting_mono R' R t); intros; apply (proj2 (H _)); assumption.
Qed.

Lemma ty_atoms_sub : forall X L T, ~ In X (ty_atoms T) ->
    ~ In X L -> ~ In X (L ++ ty_atoms T).
Proof.
  intros X L T H1 H2 H. apply in_app_or in H. tauto.
Qed.

Lemma value_relation_update_fresh : forall eta rho X a T v,
    ~ In X (ty_atoms T) ->
    (value_relation eta (relation_update rho X a) T v <->
     value_relation eta rho T v).
Proof.
  intros eta rho X a T. revert eta rho X a.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH| |];
    intros eta rho X a v Hfresh; simpl in *.
  - tauto.
  - unfold relation_update. destruct (Nat.eqb_spec X Y); simpl in *.
    + split; intro; exfalso; apply Hfresh; simpl; auto.
    + tauto.
  - assert (H1 : ~ In X (ty_atoms T1)).
    { intro Hmem. apply Hfresh. rewrite in_app_iff. left. exact Hmem. }
    assert (H2 : ~ In X (ty_atoms T2)).
    { intro Hmem. apply Hfresh. rewrite in_app_iff. right. exact Hmem. }
    split.
    + intros Hrel. destruct Hrel as [Hv [U [body [Heq Hfun]]]]. split; [exact Hv|].
      exists U, body. split; [exact Heq|]. intros arg Harg.
      apply (proj1 (expression_lifting_iff _ _ _ (fun z => IH2 eta rho X a z H2))).
      apply Hfun. apply (proj2 (IH1 eta rho X a arg H1)). exact Harg.
    + intros Hrel. destruct Hrel as [Hv [U [body [Heq Hfun]]]]. split; [exact Hv|].
      exists U, body. split; [exact Heq|]. intros arg Harg.
      apply (proj2 (expression_lifting_iff _ _ _ (fun z => IH2 eta rho X a z H2))).
      apply Hfun. apply (proj1 (IH1 eta rho X a arg H1)). exact Harg.
  - split.
    + intros Hrel. destruct Hrel as [Hv [body [Heq Hfun]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros U c HU.
      apply (proj1 (expression_lifting_iff _ _ _ (fun z => IH (c :: eta) rho X a z Hfresh))).
      apply Hfun; assumption.
    + intros Hrel. destruct Hrel as [Hv [body [Heq Hfun]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros U c HU.
      apply (proj2 (expression_lifting_iff _ _ _ (fun z => IH (c :: eta) rho X a z Hfresh))).
      apply Hfun; assumption.
  - tauto.
  - tauto.
Qed.

Fixpoint insert_after (k : nat) (a : value_candidate)
    (eta : list value_candidate) : list value_candidate :=
  match k, eta with
  | O, _ => a :: eta
  | S k', [] => []
  | S k', b :: eta' => b :: insert_after k' a eta'
  end.

Lemma insert_after_S : forall k a b eta,
    insert_after (S k) a (b :: eta) = b :: insert_after k a eta.
Proof. reflexivity. Qed.

Lemma insert_after_nth : forall k a eta i,
    i < k -> nth_error (insert_after k a eta) i = nth_error eta i.
Proof.
  induction k as [|k IH]; intros a eta i Hi; [lia|].
  destruct eta as [|b eta].
  - destruct i; simpl; auto.
  - destruct i as [|i].
    + reflexivity.
    + simpl. apply IH. lia.
Qed.

Lemma value_relation_insert : forall k eta rho a T v,
    lc_ty_at k T ->
    (value_relation eta rho T v <->
     value_relation (insert_after k a eta) rho T v).
Proof.
  intros k eta rho a T v. revert k eta rho a v.
  induction T as [i|X|T1 IH1 T2 IH2|T IH| |];
    intros k eta rho a v Hlc; simpl in *.
  - inversion Hlc. split.
    + intro Hrel. unfold value_relation in *.
      rewrite (insert_after_nth k a eta i H1). exact Hrel.
    + intro Hrel. unfold value_relation in *.
      rewrite (insert_after_nth k a eta i H1) in Hrel. exact Hrel.
  - split; intro H; exact H.
  - inversion Hlc as [K i H1| | | | |]. split.
    + intros Hrel. destruct Hrel as [Hv [U [body [Heq Hfun]]]]. split; [exact Hv|].
      exists U, body. split; [exact Heq|]. intros arg Harg.
      apply expression_lifting_mono with (R := value_relation eta rho T2)
        (R' := value_relation (insert_after k a eta) rho T2).
      * intros z Hz. apply IH2 with (k := k); assumption.
      * apply Hfun. apply (proj2 (IH1 k eta rho a arg H)). exact Harg.
    + intros Hrel. destruct Hrel as [Hv [U [body [Heq Hfun]]]]. split; [exact Hv|].
      exists U, body. split; [exact Heq|]. intros arg Harg.
      apply expression_lifting_mono with (R := value_relation (insert_after k a eta) rho T2)
        (R' := value_relation eta rho T2).
      * intros z Hz. apply (proj2 (IH2 k eta rho a z H0)). exact Hz.
      * apply Hfun. apply (proj1 (IH1 k eta rho a arg H)). exact Harg.
  - inversion Hlc as [K i H1| | | | |]. split.
    + intros Hrel. destruct Hrel as [Hv [body [Heq Hfun]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros U c HU.
      apply expression_lifting_mono with (R := value_relation (c :: eta) rho T)
        (R' := value_relation (c :: insert_after k a eta) rho T).
      * intros z Hz. rewrite <- (insert_after_S k a c eta). apply IH with (k := S k); assumption.
      * apply Hfun; assumption.
    + intros Hrel. destruct Hrel as [Hv [body [Heq Hfun]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros U c HU.
      apply expression_lifting_mono with (R := value_relation (c :: insert_after k a eta) rho T)
        (R' := value_relation (c :: eta) rho T).
      * intros z Hz. apply (proj2 (IH (S k) (c :: eta) rho a z H)). exact Hz.
      * apply Hfun; assumption.
  - split; intro H; exact H.
  - split; intro H; exact H.
Qed.

Lemma value_relation_open : forall k eta rho X a T v,
    lc_ty_at (S k) T -> nth_error eta k = Some a ->
    ~ In X (ty_atoms T) ->
    (value_relation eta (relation_update rho X a)
       (open_ty_rec k (Ty_FVar X) T) v <->
     value_relation eta rho T v).
Proof.
  intros k eta rho X a T v. revert k eta rho X a v.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH| |];
    intros k eta rho X a v Hlc Heta Hfresh; simpl in *.
  - inversion Hlc. split; intro Hrel.
    + destruct (Nat.eqb_spec k i) as [E|E].
      * unfold relation_update in Hrel. simpl in Hrel.
        destruct (Nat.eqb_spec X X) as [E2|E2].
        { simpl in Hrel. rewrite <- E. rewrite Heta. exact Hrel. }
        { exfalso. apply E2. reflexivity. }
      * exact Hrel.
    + destruct (Nat.eqb_spec k i) as [E|E].
      * rewrite <- E in Hrel. rewrite Heta in Hrel.
        unfold relation_update. simpl.
        destruct (Nat.eqb_spec X X) as [E2|E2].
        { simpl. exact Hrel. }
        { exfalso. apply E2. reflexivity. }
      * exact Hrel.
  - unfold relation_update. destruct (Nat.eqb_spec X Y) as [E|E].
    + exfalso. apply Hfresh. simpl. subst Y. auto.
    + split; intro H; exact H.
  - assert (H1 : ~ In X (ty_atoms T1)).
    { intro Hmem. apply Hfresh. rewrite in_app_iff. left. exact Hmem. }
    assert (H2 : ~ In X (ty_atoms T2)).
    { intro Hmem. apply Hfresh. rewrite in_app_iff. right. exact Hmem. }
    inversion Hlc. split.
    + intros Hrel. destruct Hrel as [Hv [U [body [Heq Hfun]]]]. split; [exact Hv|].
      exists U, body. split; [exact Heq|]. intros arg Harg.
      apply expression_lifting_mono with
        (R := value_relation eta (relation_update rho X a)
          (open_ty_rec k (Ty_FVar X) T2))
        (R' := value_relation eta rho T2).
      * intros z Hz. apply (proj1 (IH2 k eta rho X a z H5 Heta H2)). exact Hz.
      * apply Hfun. apply (proj2 (IH1 k eta rho X a arg H4 Heta H1)). exact Harg.
    + intros Hrel. destruct Hrel as [Hv [U [body [Heq Hfun]]]]. split; [exact Hv|].
      exists U, body. split; [exact Heq|]. intros arg Harg.
      apply expression_lifting_mono with
        (R := value_relation eta rho T2)
        (R' := value_relation eta (relation_update rho X a)
          (open_ty_rec k (Ty_FVar X) T2)).
      * intros z Hz. apply (proj2 (IH2 k eta rho X a z H5 Heta H2)). exact Hz.
      * apply Hfun. apply (proj1 (IH1 k eta rho X a arg H4 Heta H1)). exact Harg.
  - assert (H1 : ~ In X (ty_atoms T)). exact Hfresh.
    inversion Hlc. split.
    + intros Hrel. destruct Hrel as [Hv [body [Heq Hfun]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros U c HU.
      apply expression_lifting_mono with
        (R := value_relation (c :: eta) (relation_update rho X a)
          (open_ty_rec (S k) (Ty_FVar X) T))
        (R' := value_relation (c :: eta) rho T).
      * intros z Hz.
        assert (Heta' : nth_error (c :: eta) (S k) = Some a) by (simpl; exact Heta).
        apply (proj1 (IH (S k) (c :: eta) rho X a z H2 Heta' H1)). exact Hz.
      * apply Hfun; assumption.
    + intros Hrel. destruct Hrel as [Hv [body [Heq Hfun]]]. split; [exact Hv|].
      exists body. split; [exact Heq|]. intros U c HU.
      apply expression_lifting_mono with
        (R := value_relation (c :: eta) rho T)
        (R' := value_relation (c :: eta) (relation_update rho X a)
          (open_ty_rec (S k) (Ty_FVar X) T)).
      * intros z Hz.
        assert (Heta' : nth_error (c :: eta) (S k) = Some a) by (simpl; exact Heta).
        apply (proj2 (IH (S k) (c :: eta) rho X a z H2 Heta' H1)). exact Hz.
      * apply Hfun; assumption.
  - tauto.
  - tauto.
Qed.

Definition theta_update (theta : type_substitution) (X : atom) (U : ty) : type_substitution :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Lemma open_ty_lc : forall d k T U,
    d <= k -> lc_ty_at d T -> open_ty_rec k U T = T.
Proof.
  intros d k T U. revert d k U.
  induction T as [i|X|T1 IH1 T2 IH2|T IH| |];
    intros d k U Hd H; simpl in *.
  - inversion H. destruct (Nat.eqb_spec k i); [lia|reflexivity].
  - reflexivity.
  - inversion H. rewrite (IH1 d k U Hd H3), (IH2 d k U Hd H4). reflexivity.
  - inversion H. f_equal. apply (IH (S d) (S k) U); [lia|assumption].
  - reflexivity.
  - reflexivity.
Qed.

Lemma instantiate_ty_open : forall theta X U k T,
    type_substitution_closed theta -> locally_closed_ty U ->
    ~ In X (ty_atoms T) ->
    instantiate_ty (theta_update theta X U)
      (open_ty_rec k (Ty_FVar X) T) =
    open_ty_rec k U (instantiate_ty theta T).
Proof.
  intros theta X U k T. revert theta X U k.
  induction T as [i|Y|T1 IH1 T2 IH2|T IH| |];
    intros theta X U k Htheta HU Hfresh; simpl in *.
  - destruct (Nat.eqb_spec k i) as [E|E].
    + subst i. simpl. unfold theta_update.
      destruct (Nat.eqb_spec X X) as [E2|E2].
      * simpl. reflexivity.
      * exfalso. apply E2. reflexivity.
    + simpl. reflexivity.
  - unfold theta_update. destruct (Nat.eqb_spec X Y) as [E|E].
    + exfalso. apply Hfresh. simpl. subst Y. auto.
    + simpl. rewrite (open_ty_lc 0 k (theta Y) U).
      * reflexivity.
      * lia.
      * apply Htheta.
  - assert (H1 : ~ In X (ty_atoms T1)).
    { intro Hmem. apply Hfresh. rewrite in_app_iff. left. exact Hmem. }
    assert (H2 : ~ In X (ty_atoms T2)).
    { intro Hmem. apply Hfresh. rewrite in_app_iff. right. exact Hmem. }
    rewrite (IH1 theta X U k Htheta HU H1),
      (IH2 theta X U k Htheta HU H2). reflexivity.
  - rewrite (IH theta X U (S k) Htheta HU Hfresh). reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma open_tm_ty_lc_at : forall D K k t U,
    D <= K -> lc_tm_at D k t -> open_tm_ty_rec K U t = t.
Proof.
  intros D K k t U. revert D K k U.
  induction t as [i|x|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |t1 IH1 t2 IH2 t3 IH3| |t IH|n IHn b IHb s IHs];
    intros D K k U HD Hlc; simpl in *.
  - inversion Hlc. reflexivity.
  - reflexivity.
  - inversion Hlc. f_equal.
    + apply open_ty_lc with (d := D); [assumption|assumption].
    + apply (IH D K (S k) U); [assumption|assumption].
  - inversion Hlc. f_equal.
    + apply (IH1 D K k U); assumption.
    + apply (IH2 D K k U); assumption.
  - inversion Hlc. f_equal. apply (IH (S D) (S K) k U); [lia|assumption].
  - inversion Hlc. f_equal.
    + apply (IH D K k U); assumption.
    + apply open_ty_lc with (d := D); [assumption|assumption].
  - reflexivity.
  - reflexivity.
  - inversion Hlc. f_equal.
    + apply (IH1 D K k U); assumption.
    + apply (IH2 D K k U); assumption.
    + apply (IH3 D K k U); assumption.
  - reflexivity.
  - inversion Hlc. f_equal. apply (IH D K k U); assumption.
  - inversion Hlc. f_equal.
    + apply (IHn D K k U); assumption.
    + apply (IHb D K k U); assumption.
    + apply (IHs D K k U); assumption.
Qed.

Lemma open_tm_ty_lc : forall K t U,
    locally_closed_tm t -> open_tm_ty_rec K U t = t.
Proof.
  intros K t U H. apply (open_tm_ty_lc_at 0 K 0 t U); [lia|exact H].
Qed.

Lemma instantiate_open : forall theta gamma X U k t,
    type_substitution_closed theta -> locally_closed_ty U ->
    term_substitution_closed gamma ->
    ~ In X (tm_ty_atoms t) ->
    instantiate (theta_update theta X U) gamma
      (open_tm_ty_rec k (Ty_FVar X) t) =
    open_tm_ty_rec k U (instantiate theta gamma t).
Proof.
  intros theta gamma X U k t. revert theta gamma X U k.
  induction t as [i|y|T t IH|t1 IH1 t2 IH2|t IH|t IH| | |t1 IH1 t2 IH2 t3 IH3| |t IH|n IHn b IHb s IHs];
    intros theta gamma X U k Htheta HU Hgamma Hfresh; simpl in *.
  - reflexivity.
  - rewrite (open_tm_ty_lc_at 0 k 0 (gamma y) U); [reflexivity|lia|apply Hgamma].
  - assert (HT : ~ In X (ty_atoms T)).
    { intro H. apply Hfresh. rewrite in_app_iff. left. exact H. }
    assert (Hbody : ~ In X (tm_ty_atoms t)).
    { intro H. apply Hfresh. rewrite in_app_iff. right. exact H. }
    rewrite (instantiate_ty_open theta X U k T Htheta HU HT).
    rewrite (IH theta gamma X U k Htheta HU Hgamma Hbody). reflexivity.
  - assert (H1 : ~ In X (tm_ty_atoms t1)).
    { intro H. apply Hfresh. rewrite in_app_iff. left. exact H. }
    assert (H2 : ~ In X (tm_ty_atoms t2)).
    { intro H. apply Hfresh. rewrite in_app_iff. right. exact H. }
    rewrite (IH1 theta gamma X U k Htheta HU Hgamma H1),
      (IH2 theta gamma X U k Htheta HU Hgamma H2). reflexivity.
  - rewrite (IH theta gamma X U (S k) Htheta HU Hgamma Hfresh). reflexivity.
  - assert (H1 : ~ In X (tm_ty_atoms t)).
    { intro H. apply Hfresh. rewrite in_app_iff. left. exact H. }
    assert (H2 : ~ In X (ty_atoms t0)).
    { intro H. apply Hfresh. rewrite in_app_iff. right. exact H. }
    rewrite (IH theta gamma X U k Htheta HU Hgamma H1).
    rewrite (instantiate_ty_open theta X U k t0 Htheta HU H2). reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (H1 : ~ In X (tm_ty_atoms t1)).
    { intro H. apply Hfresh. rewrite in_app_iff. left. exact H. }
    assert (H2 : ~ In X (tm_ty_atoms t2)).
    { intro H. apply Hfresh. rewrite in_app_iff. right. rewrite in_app_iff. left. exact H. }
    assert (H3 : ~ In X (tm_ty_atoms t3)).
    { intro H. apply Hfresh. rewrite in_app_iff. right. rewrite in_app_iff. right. exact H. }
    rewrite (IH1 theta gamma X U k Htheta HU Hgamma H1),
      (IH2 theta gamma X U k Htheta HU Hgamma H2),
      (IH3 theta gamma X U k Htheta HU Hgamma H3). reflexivity.
  - reflexivity.
  - rewrite (IH theta gamma X U k Htheta HU Hgamma Hfresh). reflexivity.
  - assert (H1 : ~ In X (tm_ty_atoms n)).
    { intro H. apply Hfresh. rewrite in_app_iff. left. exact H. }
    assert (H2 : ~ In X (tm_ty_atoms b)).
    { intro H. apply Hfresh. rewrite in_app_iff. right. rewrite in_app_iff. left. exact H. }
    assert (H3 : ~ In X (tm_ty_atoms s)).
    { intro H. apply Hfresh. rewrite in_app_iff. right. rewrite in_app_iff. right. exact H. }
    rewrite (IHn theta gamma X U k Htheta HU Hgamma H1),
      (IHb theta gamma X U k Htheta HU Hgamma H2),
      (IHs theta gamma X U k Htheta HU Hgamma H3). reflexivity.
Qed.

Lemma lc_ty_type_weak_n : forall K T,
    lc_ty_at 0 T -> lc_ty_at K T.
Proof.
  induction K as [|K IH]; intros T H; [exact H|].
  apply lc_ty_weak. apply IH. assumption.
Qed.

Lemma lc_ty_instantiate : forall theta K T,
    type_substitution_closed theta -> lc_ty_at K T ->
    lc_ty_at K (instantiate_ty theta T).
Proof.
  intros theta K T Htheta H. induction H.
  - constructor. assumption.
  - apply lc_ty_type_weak_n. apply Htheta.
  - constructor; assumption.
  - constructor. assumption.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_closed_weaken : forall K k t,
    locally_closed_tm t -> lc_tm_at K k t.
Proof.
  intros K k t H. unfold locally_closed_tm in H.
  induction K as [|K IHK].
  - induction k as [|k IHk].
    + exact H.
    + apply lc_tm_weak. apply IHk.
  - apply lc_tm_type_weak. apply IHK.
Qed.

Lemma lc_tm_instantiate : forall theta gamma K k t,
    type_substitution_closed theta -> term_substitution_closed gamma ->
    lc_tm_at K k t -> lc_tm_at K k (instantiate theta gamma t).
Proof.
  intros theta gamma K k t Htheta Hgamma H. induction H.
  - simpl. constructor. assumption.
  - simpl. apply lc_tm_closed_weaken. apply Hgamma.
  - simpl. constructor.
    + apply lc_ty_instantiate; assumption.
    + apply IHlc_tm_at; assumption.
  - simpl. constructor; assumption.
  - simpl. constructor; assumption.
  - simpl. constructor.
    + apply IHlc_tm_at; assumption.
    + apply lc_ty_instantiate; assumption.
  - constructor.
  - constructor.
  - constructor.
    + apply IHlc_tm_at1; assumption.
    + apply IHlc_tm_at2; assumption.
    + apply IHlc_tm_at3; assumption.
  - constructor.
  - simpl. constructor. apply IHlc_tm_at; assumption.
  - simpl. constructor.
    + apply IHlc_tm_at1; assumption.
    + apply IHlc_tm_at2; assumption.
    + apply IHlc_tm_at3; assumption.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationIfRecursionMediumTask.
