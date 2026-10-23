(** System F CBV strong-normalization benchmark, Hard variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFNormalizationIfRecursionHardTask.

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

(* Type erasure leaves the term-level computation intact while making all
   type annotations irrelevant to the reducibility argument. *)
Fixpoint erase_tm (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i | tm_fvar x => tm_fvar x
  | tm_abs _ b => tm_abs Ty_Bool (erase_tm b)
  | tm_app f a => tm_app (erase_tm f) (erase_tm a)
  | tm_tabs b => tm_tabs (erase_tm b)
  | tm_tapp f _ => tm_tapp (erase_tm f) Ty_Bool
  | tm_true => tm_true | tm_false => tm_false
  | tm_if c a b => tm_if (erase_tm c) (erase_tm a) (erase_tm b)
  | tm_zero => tm_zero | tm_succ n => tm_succ (erase_tm n)
  | tm_natrec n b s => tm_natrec (erase_tm n) (erase_tm b) (erase_tm s)
  end.

Lemma erase_open_tm_rec : forall t k u,
  erase_tm (open_tm_rec k u t) = open_tm_rec k (erase_tm u) (erase_tm t).
Proof.
  induction t; intros k u; simpl; try rewrite IHt; try rewrite IHt1; try rewrite IHt2;
    try rewrite IHt3; try reflexivity.
  - destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma erase_open_tm : forall t u,
  erase_tm (open_tm t u) = open_tm (erase_tm t) (erase_tm u).
Proof. intros; apply erase_open_tm_rec. Qed.

Lemma erase_open_tm_ty_rec : forall t k U,
  erase_tm (open_tm_ty_rec k U t) = erase_tm t.
Proof.
  induction t; intros k U; simpl; try rewrite IHt; try rewrite IHt1;
    try rewrite IHt2; try rewrite IHt3; reflexivity.
Qed.
Lemma erase_open_tm_ty : forall t U, erase_tm (open_tm_ty t U) = erase_tm t.
Proof. intros; apply erase_open_tm_ty_rec. Qed.
Lemma open_erased_tm_ty_bool_rec : forall t k,
  open_tm_ty_rec k Ty_Bool (erase_tm t) = erase_tm t.
Proof.
  induction t; intros k; simpl; try rewrite IHt; try rewrite IHt1;
    try rewrite IHt2; try rewrite IHt3; reflexivity.
Qed.
Lemma open_erased_tm_ty_bool : forall t,
  open_tm_ty (erase_tm t) Ty_Bool = erase_tm t.
Proof. intros; apply open_erased_tm_ty_bool_rec. Qed.

Lemma erase_lc : forall K k t, lc_tm_at K k t -> lc_tm_at K k (erase_tm t).
Proof. intros K k t H; induction H; simpl; eauto using lc_tm_at. Qed.

Lemma erase_lc_any : forall K K' k t, lc_tm_at K k t -> lc_tm_at K' k (erase_tm t).
Proof.
  intros K K' k t H; revert K'; induction H; intros K'; simpl.
  - constructor; assumption.
  - constructor.
  - apply lc_tm_abs; [constructor|]. apply IHlc_tm_at; exact K'.
  - apply lc_tm_app; [apply IHlc_tm_at1|apply IHlc_tm_at2]; exact K'.
  - apply lc_tm_tabs. apply IHlc_tm_at; exact (S K').
  - apply lc_tm_tapp; [apply IHlc_tm_at; exact K'|constructor].
  - constructor.
  - constructor.
  - apply lc_tm_if; [apply IHlc_tm_at1|apply IHlc_tm_at2|apply IHlc_tm_at3]; exact K'.
  - constructor.
  - apply lc_tm_succ; apply IHlc_tm_at; exact K'.
  - apply lc_tm_rec; [apply IHlc_tm_at1|apply IHlc_tm_at2|apply IHlc_tm_at3]; exact K'.
Qed.


Lemma erase_locally_closed : forall t, locally_closed_tm t -> locally_closed_tm (erase_tm t).
Proof. intros; apply erase_lc; assumption. Qed.
Lemma erase_numeric_value : forall n, numeric_value n -> numeric_value (erase_tm n).
Proof. intros n H; induction H; simpl; constructor; assumption. Qed.
Lemma erase_value : forall v, value v -> value (erase_tm v).
Proof.
  intros v H; inversion H; subst; simpl.
  - apply v_abs. change (locally_closed_tm (erase_tm (tm_abs T t))).
    apply erase_locally_closed; assumption.
  - apply v_tabs. change (locally_closed_tm (erase_tm (tm_tabs t))).
    apply erase_locally_closed; assumption.
  - apply v_true.
  - apply v_false.
  - apply v_nat; eapply erase_numeric_value; eassumption.
Qed.

Lemma step_erase : forall t u, t --> u -> erase_tm t --> erase_tm u.
Proof.
  intros t u H; induction H; simpl.
  - rewrite erase_open_tm. apply ST_AppAbs.
    + change (locally_closed_tm (erase_tm (tm_abs T t))). apply erase_locally_closed; assumption.
    + apply erase_value; assumption.
  - apply ST_App1; eauto using erase_locally_closed.
  - apply ST_App2; eauto using erase_value.
  - rewrite erase_open_tm_ty. rewrite <- open_erased_tm_ty_bool at 2.
    apply ST_TAppTabs.
    + change (locally_closed_tm (erase_tm (tm_tabs t))). apply erase_locally_closed; assumption.
    + constructor.
  - apply ST_TApp; [assumption|constructor].
  - apply ST_Succ; assumption.
  - apply ST_RecArg; eauto using erase_locally_closed, erase_numeric_value.
  - apply ST_RecBase; eauto using erase_locally_closed, erase_numeric_value.
  - apply ST_RecStep; eauto using erase_numeric_value, erase_value.
  - apply ST_RecZero; eauto using erase_value.
  - apply ST_RecSucc; eauto using erase_numeric_value, erase_value.
  - apply ST_IfTrue; eauto using erase_locally_closed.
  - apply ST_IfFalse; eauto using erase_locally_closed.
  - apply ST_If; eauto using erase_locally_closed.
Qed.

(* Basic closure facts for strongly_normalizing and values. *)
Lemma lc_ty_at_mono : forall K K' T, K <= K' -> lc_ty_at K T -> lc_ty_at K' T.
Proof.
  intros K K' T Hle H; revert K' Hle; induction H; intros K' Hle.
  - apply lc_ty_bvar; lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all; apply IHlc_ty_at; lia.
  - apply lc_ty_bool.
  - apply lc_ty_nat.
Qed.

Lemma lc_tm_at_mono : forall K k K' k' t,
  K <= K' -> k <= k' -> lc_tm_at K k t -> lc_tm_at K' k' t.
Proof.
  intros K k K' k' t HK Hk H; revert K' k' HK Hk; induction H; intros K' k' HK Hk.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + eapply lc_ty_at_mono; eauto.
    + apply IHlc_tm_at; [exact HK|lia].
  - eapply lc_tm_app; eauto.
  - apply lc_tm_tabs; eapply IHlc_tm_at; eauto; lia.
  - eapply lc_tm_tapp; eauto using lc_ty_at_mono.
  - apply lc_tm_true.
  - apply lc_tm_false.
  - eapply lc_tm_if; eauto.
  - apply lc_tm_zero.
  - apply lc_tm_succ; eauto.
  - eapply lc_tm_rec; eauto.
Qed.

Lemma open_ty_lc : forall K T U,
  lc_ty_at (S K) T -> lc_ty_at K U -> lc_ty_at K (open_ty_rec K U T).
Proof.
  intros K T; revert K; induction T; intros K U HT HU; simpl in *.
  - inversion HT; subst. destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact HU.
    + apply lc_ty_bvar. apply Nat.eqb_neq in E; lia.
  - inversion HT; constructor.
  - inversion HT; subst; constructor; eauto.
  - inversion HT; subst. constructor. eapply IHT; eauto.
    apply (lc_ty_at_mono K (S K) U); [lia|exact HU].
  - constructor.
  - constructor.
Qed.

Lemma open_tm_ty_lc : forall K k t U,
  lc_tm_at (S K) k t -> lc_ty_at K U ->
  lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k t; revert K k; induction t; intros K k U Ht HU; simpl in *.
  - inversion Ht; subst; constructor; assumption.
  - inversion Ht; subst; constructor.
  - inversion Ht; subst. apply lc_tm_abs.
    + eapply open_ty_lc; eassumption.
    + eapply IHt; eassumption.
  - inversion Ht; subst. apply lc_tm_app.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
  - inversion Ht; subst. apply lc_tm_tabs.
    eapply IHt; [eassumption|]. apply (lc_ty_at_mono K (S K) U); [lia|exact HU].
  - inversion Ht; subst. apply lc_tm_tapp.
    + eapply IHt; eassumption.
    + eapply open_ty_lc; eassumption.
  - inversion Ht; subst; apply lc_tm_true.
  - inversion Ht; subst; apply lc_tm_false.
  - inversion Ht; subst. apply lc_tm_if.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
    + eapply IHt3; eassumption.
  - inversion Ht; subst; apply lc_tm_zero.
  - inversion Ht; subst. apply lc_tm_succ. eapply IHt; eassumption.
  - inversion Ht; subst. apply lc_tm_rec.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
    + eapply IHt3; eassumption.
Qed.

Lemma open_tm_lc : forall K k t u,
  lc_tm_at K (S k) t -> lc_tm_at K k u ->
  lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k t; revert K k; induction t; intros K k u Ht Hu; simpl in *.
  - inversion Ht; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact Hu.
    + apply lc_tm_bvar. apply Nat.eqb_neq in E; inversion Ht; subst; lia.
  - inversion Ht; subst; apply lc_tm_fvar.
  - inversion Ht; subst. apply lc_tm_abs.
    + assumption.
    + eapply IHt; [eassumption|]. apply (lc_tm_at_mono K k K (S k)); [lia|lia|exact Hu].
  - inversion Ht; subst. apply lc_tm_app.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
  - inversion Ht; subst. apply lc_tm_tabs.
    eapply IHt with (K:=S K) (k:=k) (u:=u); [eassumption|].
    apply (lc_tm_at_mono K k (S K) k); [lia|lia|exact Hu].
  - inversion Ht; subst. apply lc_tm_tapp; [eapply IHt; eassumption|assumption].
  - inversion Ht; subst; apply lc_tm_true.
  - inversion Ht; subst; apply lc_tm_false.
  - inversion Ht; subst. apply lc_tm_if.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
    + eapply IHt3; eassumption.
  - inversion Ht; subst; apply lc_tm_zero.
  - inversion Ht; subst. apply lc_tm_succ. eapply IHt; eassumption.
  - inversion Ht; subst. apply lc_tm_rec.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
    + eapply IHt3; eassumption.
Qed.

Lemma open_tm_lc_inverse : forall K k t u,
  lc_tm_at K k u -> lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k; induction t; intros K k u Hu Hopen; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion Hopen; subst. apply lc_tm_bvar. apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion Hopen; subst. apply lc_tm_abs; [assumption|].
    eapply IHt with (K:=K) (k:=S k) (u:=u).
    + exact (lc_tm_at_mono K k K (S k) u (le_n K) (Nat.le_succ_diag_r k) Hu).
    + assumption.
  - inversion Hopen; subst. apply lc_tm_app.
    + exact (IHt1 K k u Hu H3).
    + exact (IHt2 K k u Hu H4).
  - inversion Hopen; subst. apply lc_tm_tabs. eapply IHt with (K:=S K) (k:=k) (u:=u).
    + exact (lc_tm_at_mono K k (S K) k u (Nat.le_succ_diag_r K) (le_n k) Hu).
    + assumption.
  - inversion Hopen; subst. apply lc_tm_tapp.
    + exact (IHt K k u Hu H3).
    + assumption.
  - constructor.
  - constructor.
  - inversion Hopen; subst. apply lc_tm_if.
    + exact (IHt1 K k u Hu H4).
    + exact (IHt2 K k u Hu H5).
    + exact (IHt3 K k u Hu H6).
  - constructor.
  - inversion Hopen; subst. apply lc_tm_succ. exact (IHt K k u Hu H2).
  - inversion Hopen; subst. apply lc_tm_rec.
    + exact (IHt1 K k u Hu H4).
    + exact (IHt2 K k u Hu H5).
    + exact (IHt3 K k u Hu H6).
Qed.


Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof. intros n H; induction H; unfold locally_closed_tm in *; eauto using lc_tm_at. Qed.
Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst.
  - assumption.
  - assumption.
  - unfold locally_closed_tm; constructor.
  - unfold locally_closed_tm; constructor.
  - apply numeric_value_lc; assumption.
Qed.

Lemma step_lc : forall t u, locally_closed_tm t -> t --> u -> locally_closed_tm u.
Proof.
  intros t u Hlc Hs; induction Hs; unfold locally_closed_tm in *.
  - inversion Hlc; subst. inversion H; subst. eapply open_tm_lc; eauto using value_lc.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. inversion H; subst. eapply open_tm_ty_lc; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. assumption.
  - inversion Hlc; subst. apply lc_tm_app.
    + apply lc_tm_app; [apply value_lc; exact H1|apply numeric_value_lc; exact H].
    + apply lc_tm_rec; [apply numeric_value_lc; exact H|apply value_lc; exact H0|apply value_lc; exact H1].
  - inversion Hlc; subst. assumption.
  - inversion Hlc; subst. assumption.
  - inversion Hlc; subst. constructor; eauto.
Qed.

Lemma SN_step : forall t u, strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof.
  intros t u H; inversion H; eauto.
Qed.

Lemma SN_multi : forall t u, strongly_normalizing t -> t -->* u -> strongly_normalizing u.
Proof.
  intros t u Hsn Hm; induction Hm; eauto using SN_step.
Qed.

Lemma SN_intro_from_steps : forall t,
  (forall u, t --> u -> strongly_normalizing u) -> strongly_normalizing t.
Proof. intros; constructor; assumption. Qed.

Lemma value_no_step : forall v u, value v -> ~ (v --> u).
Proof.
  intros v u Hv; induction Hv; intros Hs.
  - inversion Hs.
  - inversion Hs.
  - inversion Hs.
  - inversion Hs.
  - generalize dependent u. induction H; intros u Hs.
    + inversion Hs.
    + inversion Hs; subst. eapply IHnumeric_value; eassumption.
Qed.

Lemma SN_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros; constructor; intros u Hs; exfalso; eapply value_no_step; eauto.
Qed.

Lemma numeric_value_value : forall n, numeric_value n -> value n.
Proof. intros; constructor; assumption. Qed.


Fixpoint subst_env (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i | tm_fvar x => sigma x
  | tm_abs T b => tm_abs T (subst_env sigma b)
  | tm_app f a => tm_app (subst_env sigma f) (subst_env sigma a)
  | tm_tabs b => tm_tabs (subst_env sigma b)
  | tm_tapp f T => tm_tapp (subst_env sigma f) T
  | tm_true => tm_true | tm_false => tm_false
  | tm_if c a b => tm_if (subst_env sigma c) (subst_env sigma a) (subst_env sigma b)
  | tm_zero => tm_zero | tm_succ n => tm_succ (subst_env sigma n)
  | tm_natrec n b s => tm_natrec (subst_env sigma n) (subst_env sigma b) (subst_env sigma s)
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => [] | tm_fvar x => [x]
  | tm_abs _ b => fv_tm b
  | tm_app f a => fv_tm f ++ fv_tm a
  | tm_tabs b => fv_tm b
  | tm_tapp f _ => fv_tm f
  | tm_true | tm_false | tm_zero => []
  | tm_if c a b => fv_tm c ++ fv_tm a ++ fv_tm b
  | tm_succ n => fv_tm n
  | tm_natrec n b s => fv_tm n ++ fv_tm b ++ fv_tm s
  end.

Definition env_update (sigma : atom -> tm) (x : atom) (v : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then v else sigma y.

Lemma open_tm_rec_lc_id : forall t K d k u,
  d <= k -> lc_tm_at K d t -> open_tm_rec k u t = t.
Proof.
  induction t; intros K d k u Hdk Hlc; simpl.
  - inversion Hlc; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal. apply IHt with (K:=K) (d:=S d) (k:=S k); [lia|assumption].
  - inversion Hlc; subst. rewrite IHt1 with (K:=K) (d:=d) (k:=k); [|assumption|eassumption].
    rewrite IHt2 with (K:=K) (d:=d) (k:=k); [reflexivity|assumption|eassumption].
  - inversion Hlc; subst. f_equal. apply IHt with (K:=S K) (d:=d) (k:=k); eauto.
  - inversion Hlc; subst. rewrite IHt with (K:=K) (d:=d) (k:=k); eauto.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. rewrite IHt1 with (K:=K) (d:=d) (k:=k); [|assumption|eassumption].
    rewrite IHt2 with (K:=K) (d:=d) (k:=k); [|assumption|eassumption].
    rewrite IHt3 with (K:=K) (d:=d) (k:=k); [reflexivity|assumption|eassumption].
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHt; eauto.
  - inversion Hlc; subst. rewrite IHt1 with (K:=K) (d:=d) (k:=k); [|assumption|eassumption].
    rewrite IHt2 with (K:=K) (d:=d) (k:=k); [|assumption|eassumption].
    rewrite IHt3 with (K:=K) (d:=d) (k:=k); [reflexivity|assumption|eassumption].
Qed.

Lemma subst_env_open : forall t k x sigma v,
  ~ In x (fv_tm t) -> locally_closed_tm v ->
  (forall y, locally_closed_tm (sigma y)) ->
  subst_env (env_update sigma x v) (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k v (subst_env sigma t).
Proof.
  induction t; intros k x sigma v Hfresh Hv Hsigma; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl.
    + unfold env_update; rewrite Nat.eqb_refl; reflexivity.
    + reflexivity.
  - simpl in Hfresh. assert (Hneq : a <> x) by (intro E; apply Hfresh; left; exact E).
    assert (Heq : Nat.eqb a x = false) by (apply Nat.eqb_neq; exact Hneq).
    unfold env_update; rewrite Heq. simpl.
    rewrite open_tm_rec_lc_id with (K:=0) (d:=0) (u:=v); [reflexivity|lia|apply Hsigma].
  - f_equal. apply IHt; assumption.
  - assert (Hf1 : ~ In x (fv_tm t1)) by (intro Hin; apply Hfresh; apply in_or_app; left; exact Hin).
    assert (Hf2 : ~ In x (fv_tm t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; exact Hin).
    simpl. rewrite IHt1, IHt2; eauto.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - reflexivity.
  - assert (H1 : ~ In x (fv_tm t1)) by (intro Hin; apply Hfresh; repeat apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin).
    assert (H3 : ~ In x (fv_tm t3)) by (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin).
    simpl. rewrite IHt1, IHt2, IHt3; eauto.
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - assert (H1 : ~ In x (fv_tm t1)) by (intro Hin; apply Hfresh; repeat apply in_or_app; left; exact Hin).
    assert (H2 : ~ In x (fv_tm t2)) by (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin).
    assert (H3 : ~ In x (fv_tm t3)) by (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin).
    simpl. rewrite IHt1, IHt2, IHt3; eauto.
Qed.

Lemma erase_subst_env : forall sigma t,
  erase_tm (subst_env sigma t) = subst_env (fun x => erase_tm (sigma x)) (erase_tm t).
Proof.
  intros sigma t; induction t; simpl; try rewrite IHt; try rewrite IHt1;
    try rewrite IHt2; try rewrite IHt3; reflexivity.
Qed.

Lemma subst_env_identity : forall t, subst_env (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity. Qed.

Definition neutral (t : tm) : Prop :=
  match t with tm_abs _ _ | tm_tabs _ => False | _ => True end.

Record candidate (P : tm -> Prop) : Prop := Candidate {
  cand_lc : forall t, P t -> locally_closed_tm t;
  cand_sn : forall t, P t -> strongly_normalizing t;
  cand_step : forall t u, P t -> t --> u -> P u;
  cand_neutral : forall t, locally_closed_tm t -> neutral t ->
    (forall u, t --> u -> P u) -> P t
}.

Definition rho_ext (rho : nat -> tm -> Prop) (P : tm -> Prop) : nat -> tm -> Prop :=
  fun i => if Nat.eqb i 0 then P else rho (Nat.pred i).

Definition rho_update (rho : nat -> tm -> Prop) (k : nat) (P : tm -> Prop) : nat -> tm -> Prop :=
  fun i => if Nat.ltb i k then rho i else if Nat.eqb i k then P else rho (Nat.pred i).

Lemma rho_ext_zero : forall rho P i, rho_ext rho P i = rho_update rho 0 P i.
Proof. intros; unfold rho_ext, rho_update; destruct i; simpl; rewrite ?Nat.eqb_refl; reflexivity. Qed.

Lemma rho_update_ext : forall rho Q P k i,
  rho_update (rho_ext rho Q) (S k) P i = rho_ext (rho_update rho k P) Q i.
Proof.
  intros rho Q P k i; destruct i as [|i]; [reflexivity|].
  unfold rho_update, rho_ext; simpl.
  destruct (Nat.ltb i k) eqn:Hlt.
  - assert (E : Nat.ltb (S i) (S k) = true) by (apply Nat.ltb_lt; apply Nat.ltb_lt in Hlt; lia).
    rewrite E; reflexivity.
  - assert (E : Nat.ltb (S i) (S k) = false) by (apply Nat.ltb_ge; apply Nat.ltb_ge in Hlt; lia).
    rewrite E. destruct (Nat.eqb i k) eqn:Heq.
    + assert (Nat.eqb (S i) (S k) = true) by (apply Nat.eqb_eq; apply Nat.eqb_eq in Heq; lia).
      reflexivity.
    + assert (Nat.eqb (S i) (S k) = false) by (apply Nat.eqb_neq; apply Nat.eqb_neq in Heq; lia).
      assert (i <> 0) by (apply Nat.ltb_ge in Hlt; apply Nat.eqb_neq in Heq; lia).
      destruct i; [lia|simpl; reflexivity].
Qed.


Lemma rho_update_equiv : forall rho k P Q,
  (forall t, P t <-> Q t) -> forall i t,
  (rho_update rho k P i t <-> rho_update rho k Q i t).
Proof.
  intros rho k P Q HPQ i t; unfold rho_update.
  destruct (Nat.ltb i k); [tauto|].
  destruct (Nat.eqb i k); [apply HPQ|tauto].
Qed.

Lemma rho_ext_equiv : forall rho rho' P Q,
  (forall i t, rho i t <-> rho' i t) -> (forall t, P t <-> Q t) ->
  forall i t, rho_ext rho P i t <-> rho_ext rho' Q i t.
Proof.
  intros rho rho' P Q Hr Hp i t; unfold rho_ext.
  destruct (Nat.eqb i 0); [apply Hp|]. apply Hr.
Qed.

Fixpoint interp (rho : nat -> tm -> Prop) (xi : atom -> tm -> Prop)
    (T : ty) : tm -> Prop :=
  match T with
  | Ty_BVar i => rho i
  | Ty_FVar X => xi X
  | Ty_Arrow A B => fun f => locally_closed_tm f /\ strongly_normalizing f /\
      (forall a, interp rho xi A a -> interp rho xi B (tm_app f a))
  | Ty_All A => fun f => locally_closed_tm f /\ strongly_normalizing f /\
      (forall P, candidate P -> interp (rho_ext rho P) xi A (tm_tapp f Ty_Bool))
  | Ty_Bool => fun t => locally_closed_tm t /\ strongly_normalizing t
  | Ty_Nat => fun t => locally_closed_tm t /\ strongly_normalizing t
  end.

Lemma interp_rho_irrel : forall K T, lc_ty_at K T -> forall rho rho' xi,
  (forall i, i < K -> forall z, (rho i z <-> rho' i z)) -> forall t,
  (interp rho xi T t <-> interp rho' xi T t).
Proof.
  intros K T Hlc; induction Hlc; intros rho rho' xi Henv t; simpl.
  - specialize (Henv i H t); tauto.
  - tauto.
  - split.
    + intros [HtmLC [Hsn Hfun]]. split; [exact HtmLC|]. split; [exact Hsn|].
      intros a Ha. apply (proj1 (IHHlc2 rho rho' xi Henv (tm_app t a))).
      apply Hfun. apply (proj2 (IHHlc1 rho rho' xi Henv a)); exact Ha.
    + intros [HtmLC [Hsn Hfun]]. split; [exact HtmLC|]. split; [exact Hsn|].
      intros a Ha. apply (proj2 (IHHlc2 rho rho' xi Henv (tm_app t a))).
      apply Hfun. apply (proj1 (IHHlc1 rho rho' xi Henv a)); exact Ha.
  - split.
      
    + intros [HtmLC [Hsn Hall]]. split; [exact HtmLC|]. split; [exact Hsn|].
      intros P HP. specialize (Hall P HP).
      assert (Henv' : forall i, i < S k -> forall z, rho_ext rho P i z <-> rho_ext rho' P i z).
      { intros [|i] Hi z; unfold rho_ext; simpl; [tauto|]. apply Henv; lia. }
      apply (proj1 (IHHlc (rho_ext rho P) (rho_ext rho' P) xi Henv' (tm_tapp t Ty_Bool))). exact Hall.
    + intros [HtmLC [Hsn Hall]]. split; [exact HtmLC|]. split; [exact Hsn|].
      intros P HP. specialize (Hall P HP).
      assert (Henv' : forall i, i < S k -> forall z, rho_ext rho P i z <-> rho_ext rho' P i z).
      { intros [|i] Hi z; unfold rho_ext; simpl; [tauto|]. apply Henv; lia. }
      apply (proj2 (IHHlc (rho_ext rho P) (rho_ext rho' P) xi Henv' (tm_tapp t Ty_Bool))). exact Hall.
  - tauto.
  - tauto.
Qed.

Lemma interp_open_ty_rec : forall T k, lc_ty_at (S k) T -> forall rho xi U,
  locally_closed_ty U -> forall t,
  (interp rho xi (open_ty_rec k U T) t <->
   interp (rho_update rho k (interp rho xi U)) xi T t).
Proof.
  induction T; intros k HT rho xi U HU t; simpl in *.
  - inversion HT; subst. destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst n. unfold rho_update. rewrite Nat.ltb_irrefl, Nat.eqb_refl. tauto.
    + assert (Hnk : n < k) by (apply Nat.eqb_neq in E; inversion HT; lia).
      unfold rho_update. assert (E2 : Nat.ltb n k = true) by (apply Nat.ltb_lt; exact Hnk). rewrite E2; tauto.
  - tauto.
  - inversion HT; subst. split.
    + intros [Hlc [Hsn Hfun]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros a Ha. apply (proj1 (IHT2 k H3 rho xi U HU (tm_app t a))).
      apply Hfun. apply (proj2 (IHT1 k H2 rho xi U HU a)); exact Ha.
    + intros [Hlc [Hsn Hfun]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros a Ha. apply (proj2 (IHT2 k H3 rho xi U HU (tm_app t a))).
      apply Hfun. apply (proj1 (IHT1 k H2 rho xi U HU a)); exact Ha.
  - inversion HT; subst. split.

    + intros [Hlc [Hsn Hall]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros Q HQ. specialize (Hall Q HQ).
      assert (HPQ : forall z, interp (rho_ext rho Q) xi U z <-> interp rho xi U z).
      { intros z. assert (E0 : forall i, i < 0 -> forall y, rho_ext rho Q i y <-> rho i y) by (intros; lia).
        exact (interp_rho_irrel 0 U HU (rho_ext rho Q) rho xi E0 z). }
      assert (Henv : forall i, i < S (S k) -> forall z,
        rho_update (rho_ext rho Q) (S k) (interp (rho_ext rho Q) xi U) i z <->
        rho_ext (rho_update rho k (interp rho xi U)) Q i z).
      { intros i Hi z. rewrite rho_update_ext. unfold rho_ext.
        destruct (Nat.eqb i 0); [tauto|].
        apply rho_update_equiv; exact HPQ. }
      apply (proj1 (IHT (S k) H1 (rho_ext rho Q) xi U HU
        (tm_tapp t Ty_Bool))) in Hall.
      apply (proj1 (interp_rho_irrel (S (S k)) T H1
        (rho_update (rho_ext rho Q) (S k) (interp (rho_ext rho Q) xi U))
        (rho_ext (rho_update rho k (interp rho xi U)) Q) xi Henv
        (tm_tapp t Ty_Bool))). exact Hall.
    + intros [Hlc [Hsn Hall]]. split; [exact Hlc|]. split; [exact Hsn|].
      intros Q HQ. specialize (Hall Q HQ).
      assert (HPQ : forall z, interp (rho_ext rho Q) xi U z <-> interp rho xi U z).
      { intros z. assert (E0 : forall i, i < 0 -> forall y, rho_ext rho Q i y <-> rho i y) by (intros; lia).
        exact (interp_rho_irrel 0 U HU (rho_ext rho Q) rho xi E0 z). }
      assert (Henv : forall i, i < S (S k) -> forall z,
        rho_update (rho_ext rho Q) (S k) (interp (rho_ext rho Q) xi U) i z <->
        rho_ext (rho_update rho k (interp rho xi U)) Q i z).
      { intros i Hi z. rewrite rho_update_ext. unfold rho_ext.
        destruct (Nat.eqb i 0); [tauto|].
        apply rho_update_equiv; exact HPQ. }
      apply (proj2 (IHT (S k) H1 (rho_ext rho Q) xi U HU
        (tm_tapp t Ty_Bool))).
      apply (proj2 (interp_rho_irrel (S (S k)) T H1
        (rho_update (rho_ext rho Q) (S k) (interp (rho_ext rho Q) xi U))
        (rho_ext (rho_update rho k (interp rho xi U)) Q) xi Henv
        (tm_tapp t Ty_Bool))). exact Hall.
  - tauto.
  - tauto.
Qed.

Lemma interp_open_ty : forall T rho xi U,
  lc_ty_at 1 T -> locally_closed_ty U -> forall t,
  (interp rho xi (open_ty T U) t <->
   interp (rho_ext rho (interp rho xi U)) xi T t).
Proof.
  intros T rho xi U HT HU t. unfold open_ty.
  pose proof (interp_open_ty_rec T 0 HT rho xi U HU t) as Hopen.
  assert (Henv : forall i, i < 1 -> forall z,
    rho_update rho 0 (interp rho xi U) i z <->
    rho_ext rho (interp rho xi U) i z).
  { intros [|i] Hi z; [unfold rho_update, rho_ext; simpl; tauto|lia]. }
  split; intro H.
  - apply (proj1 (interp_rho_irrel 1 T HT
      (rho_update rho 0 (interp rho xi U))
      (rho_ext rho (interp rho xi U)) xi Henv t)).
    apply (proj1 Hopen); exact H.
  - apply (proj2 Hopen).
    apply (proj2 (interp_rho_irrel 1 T HT
      (rho_update rho 0 (interp rho xi U))
      (rho_ext rho (interp rho xi U)) xi Henv t)); exact H.
Qed.

Lemma open_ty_rec_lc_inverse : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k X Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion Hlc; subst. apply lc_ty_bvar. apply Nat.eqb_neq in E; lia.
  - constructor.
  - inversion Hlc; subst; constructor; eauto.
  - inversion Hlc; subst. constructor. eapply IHT; eauto.
  - constructor.
  - constructor.
Qed.

Lemma open_tm_ty_lc_inverse : forall k j X t,
  lc_tm_at k j (open_tm_ty_rec k (Ty_FVar X) t) -> lc_tm_at (S k) j t.
Proof.
  intros k j A t; revert k j A; induction t; intros k j A H; simpl in *.
  - inversion H; subst; constructor; assumption.
  - constructor.
  - inversion H; subst. apply lc_tm_abs.
    + eapply open_ty_rec_lc_inverse; eassumption.
    + eapply IHt with (j:=S j); eassumption.
  - inversion H; subst. apply lc_tm_app; [eapply IHt1 with (j:=j)|eapply IHt2 with (j:=j)]; eassumption.
  - inversion H; subst. apply lc_tm_tabs. eapply IHt with (k:=S k) (j:=j); eassumption.
  - inversion H; subst. apply lc_tm_tapp.
    + eapply IHt with (j:=j); eassumption.
    + eapply open_ty_rec_lc_inverse; eassumption.
  - constructor.
  - constructor.
  - inversion H; subst. apply lc_tm_if; [eapply IHt1 with (j:=j)|eapply IHt2 with (j:=j)|eapply IHt3 with (j:=j)]; eassumption.
  - constructor.
  - inversion H; subst. apply lc_tm_succ. eapply IHt with (j:=j); eassumption.
  - inversion H; subst. apply lc_tm_rec; [eapply IHt1 with (j:=j)|eapply IHt2 with (j:=j)|eapply IHt3 with (j:=j)]; eassumption.
Qed.

Fixpoint max_atoms (L : list atom) : nat :=
  match L with [] => 0 | X :: L' => Nat.max X (max_atoms L') end.
Lemma in_le_max_atoms : forall L X, In X L -> X <= max_atoms L.
Proof.
  induction L as [|a L IH]; intros X H; [contradiction|].
  simpl. destruct H as [->|H]; [apply Nat.le_max_l|eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r]].
Qed.
Lemma fresh_atom_notin : forall L : list atom, exists X, ~ In X L.
Proof.
  intros L. exists (S (max_atoms L)). intro H.
  pose proof (in_le_max_atoms L _ H); lia.
Qed.

Lemma wf_ty_extend : forall Delta Delta' T,
  (forall X, In X Delta -> In X Delta') -> wf_ty Delta T -> wf_ty Delta' T.
Proof.
  intros Delta Delta' T Hinc Hwf; revert Delta' Hinc; induction Hwf; intros Delta' Hinc.
  - apply WF_Var. eauto.
  - apply WF_Arrow; eauto.
  - apply WF_All with (L:=L). intros X HX.
    eapply H0; [exact HX|].
    intros Y HY. destruct HY as [HY|HY]; [subst; simpl; auto|right; apply Hinc; exact HY].
  - apply WF_Bool.
  - apply WF_Nat.
Qed.

Lemma wf_ty_context_equiv : forall D D' T,
  (forall X, In X D <-> In X D') -> wf_ty D T -> wf_ty D' T.
Proof. intros D D' T Hinc Hwf; eapply wf_ty_extend; [intros X HX; apply (proj1 (Hinc X)); exact HX|exact Hwf]. Qed.

Lemma open_ty_rec_lc_id : forall K k T V,
  K <= k -> lc_ty_at K T -> open_ty_rec k V T = T.
Proof.
  intros K k T V Hle Hlc; revert k V Hle; induction Hlc; intros m V Hle; simpl.
  - destruct (Nat.eqb m i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - reflexivity.
  - rewrite IHHlc1 with (k:=m) (V:=V) by assumption.
    rewrite IHHlc2 with (k:=m) (V:=V) by assumption; reflexivity.
  - f_equal. apply IHHlc with (k:=S m) (V:=V); lia.
  - reflexivity.
  - reflexivity.
Qed.

Lemma open_tm_ty_lc_id : forall K k t U,
  K <= k -> lc_tm_at K 0 t -> open_tm_ty_rec k U t = t.
Proof.
  intros K k t U Hle Hlc; revert k U Hle; induction Hlc; intros m U Hle; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite open_ty_rec_lc_id with (K:=K) (k:=m) (T:=T) (V:=U) by assumption.
    f_equal. apply IHHlc; exact Hle.
  - rewrite IHHlc1 with (k:=m) (U:=U); [|exact Hle].
    rewrite IHHlc2 with (k:=m) (U:=U); [reflexivity|exact Hle].
  - f_equal. apply IHHlc with (k:=S m) (U:=U); lia.
  - rewrite IHHlc with (k:=m) (U:=U); [|exact Hle].
    rewrite open_ty_rec_lc_id with (K:=K) (k:=m) (T:=T) (V:=U) by assumption. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHHlc1 with (k:=m) (U:=U); [|exact Hle].
    rewrite IHHlc2 with (k:=m) (U:=U); [|exact Hle].
    rewrite IHHlc3 with (k:=m) (U:=U); [reflexivity|exact Hle].
  - reflexivity.
  - f_equal. apply IHHlc; exact Hle.
  - rewrite IHHlc1 with (k:=m) (U:=U); [|exact Hle].
    rewrite IHHlc2 with (k:=m) (U:=U); [|exact Hle].
    rewrite IHHlc3 with (k:=m) (U:=U); [reflexivity|exact Hle].
Qed.

Lemma wf_ty_lc : forall T Delta, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros T Delta Hwf; induction Hwf; unfold locally_closed_ty in *.
  - constructor.
  - constructor; assumption.
  - constructor. destruct (fresh_atom_notin L) as [X HX].
    specialize (H0 X HX). eapply open_ty_rec_lc_inverse; exact H0.
  - constructor.
  - constructor.
Qed.


Lemma ty_subst_open_ty_rec : forall T k X U V,
  locally_closed_ty U ->
  ty_subst X U (open_ty_rec k V T) = open_ty_rec k (ty_subst X U V) (ty_subst X U T).
Proof.
  induction T; intros k X U V HU; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - destruct (Nat.eqb X a); [|reflexivity].
    symmetry; apply open_ty_rec_lc_id with (K:=0) (V:=ty_subst X U V); [lia|exact HU].
  - f_equal; [apply IHT1|apply IHT2]; assumption.
  - f_equal; apply IHT; assumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma wf_ty_subst_fvar_gen : forall D D' Xsub U T,
  (forall Z, In Z D <-> In Z (Xsub :: D')) ->
  wf_ty D T -> wf_ty D' U -> wf_ty D' (ty_subst Xsub U T).
Proof.
  intros D D' Xsub U T Hctx Hwf; revert D' Xsub U Hctx.
  induction Hwf; intros D' Xsub U Hctx HU; simpl.
  - destruct (Nat.eqb Xsub X) eqn:E.
    + apply Nat.eqb_eq in E; subst; exact HU.
    + apply WF_Var. apply Nat.eqb_neq in E. apply (proj1 (Hctx X)) in H.
      simpl in H. destruct H as [H|H]; [congruence|exact H].
  - apply WF_Arrow.
    + eapply IHHwf1; eauto.
    + eapply IHHwf2; eauto.
  - eapply WF_All with (L:=Xsub :: L). intros Y HY.
    assert (HYL : ~ In Y L) by (intro Hin; apply HY; simpl; right; exact Hin).
    assert (Hbody : wf_ty (Y :: Delta) (open_ty T (Ty_FVar Y))) by (apply H; exact HYL).
    assert (HU' : wf_ty (Y :: D') U).
    { eapply wf_ty_extend; [intros Z HZ; right; exact HZ|exact HU]. }
    assert (Hctx' : forall Z, In Z (Y :: Delta) <-> In Z (Xsub :: Y :: D')).
    { intros Z; split.
      - simpl. intros [E|Ein].
        + subst Z. simpl; auto.
        + apply (proj1 (Hctx Z)) in Ein. simpl in Ein. destruct Ein as [E|Ein].
          * left; exact E.
          * right; right; exact Ein.
      - simpl. intros [E|[E|Ein]].
        + subst Z. right. apply (proj2 (Hctx Xsub)); simpl; auto.
        + subst Z. left; reflexivity.
        + right. apply (proj2 (Hctx Z)); simpl; right; exact Ein. }

    pose proof (H0 Y HYL (Y :: D') Xsub U Hctx' HU') as Hsub.
    pose proof (wf_ty_lc U D' HU) as HUl.
    unfold open_ty in Hsub |- *.
    rewrite ty_subst_open_ty_rec in Hsub by exact HUl.
    assert (Hneq : Nat.eqb Xsub Y = false).
    { apply Nat.eqb_neq. intro E; apply HY; simpl; left; exact E. }
    cbn [ty_subst] in Hsub; rewrite Hneq in Hsub; simpl in Hsub. exact Hsub.
  - apply WF_Bool.
  - apply WF_Nat.
Qed.

Lemma wf_ty_subst_fvar : forall T Delta X U,
  wf_ty (X :: Delta) T -> wf_ty Delta U -> wf_ty Delta (ty_subst X U T).
Proof.
  intros T Delta X U Hwf HU. eapply wf_ty_subst_fvar_gen with (D:=X::Delta) (Xsub:=X).
  - intros Z; simpl; tauto.
  - exact Hwf.
  - exact HU.
Qed.

Fixpoint ty_fvars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fvars A ++ ty_fvars B
  | Ty_All A => ty_fvars A
  | Ty_Bool | Ty_Nat => []
  end.

Lemma ty_subst_fresh : forall T X U,
  ~ In X (ty_fvars T) -> ty_subst X U T = T.
Proof.
  induction T; intros X U H; simpl in *; try reflexivity.
  - destruct (Nat.eqb X a) eqn:E; [apply Nat.eqb_eq in E; subst; exfalso; apply H; simpl; auto|reflexivity].
  - f_equal; [apply IHT1|apply IHT2]; intro Hin; apply H; apply in_or_app; auto.
  - f_equal; apply IHT; exact H.
Qed.

Lemma has_type_wf : forall Delta Gamma t T, has_type Delta Gamma t T -> wf_ty Delta T.
Proof.
  intros Delta Gamma t T H; induction H.
  - assumption.
  - apply WF_Arrow; [assumption|].
    destruct (fresh_atom_notin L) as [x Hx]. apply (H1 x Hx).
  - inversion IHhas_type1; assumption.
  - eapply WF_All with (L:=L); intros X HX; eauto.
  - inversion IHhas_type; subst.
    destruct (fresh_atom_notin (L ++ Delta ++ ty_fvars T)) as [X Hfresh].
    assert (HX : ~ In X L) by (intro Hin; apply Hfresh; apply in_or_app; auto).
    assert (Hopen : wf_ty (X :: Delta) (open_ty T (Ty_FVar X))) by (apply H3; exact HX).
    assert (Heq : ty_subst X U (open_ty T (Ty_FVar X)) = open_ty T U).
    { pose proof (wf_ty_lc U Delta H0) as HUl. unfold open_ty.
      rewrite ty_subst_open_ty_rec by exact HUl. simpl. rewrite Nat.eqb_refl.
      rewrite ty_subst_fresh by (intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin).
      reflexivity. }
    rewrite <- Heq. eapply wf_ty_subst_fvar; eauto.
  - apply WF_Bool.
  - apply WF_Bool.
  - assumption.
  - apply WF_Nat.
  - apply WF_Nat.
  - assumption.
Qed.

Lemma has_type_lc : forall D G t T, has_type D G t T -> locally_closed_tm t.
Proof.
  intros D G t T H; induction H.
  - unfold locally_closed_tm; constructor.
  - destruct (fresh_atom_notin L) as [x Hx].
    assert (Hbody : locally_closed_tm (open_tm t2 (tm_fvar x))) by (apply H1; exact Hx).
    unfold open_tm in Hbody. apply lc_tm_abs.
    + apply wf_ty_lc with (Delta:=Delta); assumption.
    + eapply open_tm_lc_inverse with (K:=0) (k:=0) (u:=tm_fvar x).
      * unfold locally_closed_tm; constructor.
      * exact Hbody.
  - unfold locally_closed_tm in *. constructor; assumption.
  - destruct (fresh_atom_notin L) as [X HX].
    assert (Hbody : locally_closed_tm (open_tm_ty t (Ty_FVar X))) by (apply H0; exact HX).
    unfold locally_closed_tm in *. apply lc_tm_tabs.
    unfold open_tm_ty in Hbody. eapply open_tm_ty_lc_inverse; exact Hbody.
  - unfold locally_closed_tm in *. apply lc_tm_tapp.
    + exact IHhas_type.
    + apply wf_ty_lc with (Delta:=Delta); assumption.
  - unfold locally_closed_tm; constructor.
  - unfold locally_closed_tm; constructor.
  - unfold locally_closed_tm in *. apply lc_tm_if; assumption.
  - unfold locally_closed_tm; constructor.
  - unfold locally_closed_tm in *. apply lc_tm_succ; assumption.
  - unfold locally_closed_tm in *. apply lc_tm_rec; assumption.
Qed.

Lemma subst_env_lc : forall K k t sigma,
  lc_tm_at K k t -> (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k (subst_env sigma t).
Proof.
  intros K k t sigma Hlc; induction Hlc; intros Hsigma; simpl.
  - apply lc_tm_bvar; assumption.
  - apply lc_tm_at_mono with (K:=0) (k:=0); try lia. apply Hsigma.
  - apply lc_tm_abs; [assumption|]. apply IHHlc. exact Hsigma.
  - apply lc_tm_app; [apply IHHlc1|apply IHHlc2]; exact Hsigma.
  - apply lc_tm_tabs. apply IHHlc. exact Hsigma.
  - apply lc_tm_tapp; [apply IHHlc|assumption]; exact Hsigma.
  - constructor.
  - constructor.
  - apply lc_tm_if; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; exact Hsigma.
  - constructor.
  - apply lc_tm_succ; apply IHHlc; exact Hsigma.
  - apply lc_tm_rec; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; exact Hsigma.
Qed.

Definition xi_update (xi : atom -> tm -> Prop) (X : atom) (P : tm -> Prop) : atom -> tm -> Prop :=
  fun Y => if Nat.eqb Y X then P else xi Y.

Lemma interp_xi_irrel : forall T rho xi xi',
  (forall Y, In Y (ty_fvars T) -> forall z, xi Y z <-> xi' Y z) ->
  forall z, interp rho xi T z <-> interp rho xi' T z.
Proof.
  induction T; intros rho xi xi' H z; simpl in *.
  - tauto.
  - apply H; simpl; auto.
  - assert (H1 : forall Y, In Y (ty_fvars T1) -> forall z, xi Y z <-> xi' Y z).
    { intros Y HY z'; apply H; simpl; apply in_or_app; left; exact HY. }
    assert (H2 : forall Y, In Y (ty_fvars T2) -> forall z, xi Y z <-> xi' Y z).
    { intros Y HY z'; apply H; simpl; apply in_or_app; right; exact HY. }
    split.
    + intros [Hlc [Hsn Hf]]. split; [exact Hlc|]. split; [exact Hsn|]. intros a Ha.
      apply (proj1 (IHT2 rho xi xi' H2 (tm_app z a))). apply Hf.
      apply (proj2 (IHT1 rho xi xi' H1 a)); exact Ha.
    + intros [Hlc [Hsn Hf]]. split; [exact Hlc|]. split; [exact Hsn|]. intros a Ha.
      apply (proj2 (IHT2 rho xi xi' H2 (tm_app z a))). apply Hf.
      apply (proj1 (IHT1 rho xi xi' H1 a)); exact Ha.
  - assert (H1 : forall Y, In Y (ty_fvars T) -> forall z, xi Y z <-> xi' Y z) by exact H.
    split.
    + intros [Hlc [Hsn Hf]]. split; [exact Hlc|]. split; [exact Hsn|]. intros P HP.
      apply (proj1 (IHT (rho_ext rho P) xi xi' H1 (tm_tapp z Ty_Bool))). apply Hf; exact HP.
    + intros [Hlc [Hsn Hf]]. split; [exact Hlc|]. split; [exact Hsn|]. intros P HP.
      apply (proj2 (IHT (rho_ext rho P) xi xi' H1 (tm_tapp z Ty_Bool))). apply Hf; exact HP.
  - tauto.
  - tauto.
Qed.

Lemma ty_fvars_open_subset : forall T k U Y,
  In Y (ty_fvars T) -> In Y (ty_fvars (open_ty_rec k U T)).
Proof.
  induction T; intros k U Y Hin; simpl in *; try contradiction.
  - exact Hin.
  - apply in_app_or in Hin; apply in_or_app; destruct Hin; [left; eapply IHT1|right; eapply IHT2]; eauto.
  - eapply IHT; eauto.
Qed.

Lemma wf_ty_fvars : forall D T, wf_ty D T -> forall X, In X (ty_fvars T) -> In X D.
Proof.
  intros D T H; induction H; intros Y Hin; simpl in *.
  - destruct Hin as [->|[]]; assumption.
  - apply in_app_or in Hin; destruct Hin; eauto.
  - destruct (fresh_atom_notin (L ++ Delta ++ [Y])) as [A HA].
    assert (HAL : ~ In A L) by (intro E; apply HA; apply in_or_app; left; exact E).
    assert (Hsub : In Y (ty_fvars (open_ty T (Ty_FVar A))))
      by (unfold open_ty; eapply ty_fvars_open_subset; exact Hin).
    specialize (H0 A HAL Y Hsub). simpl in H0. destruct H0 as [E|E].
    + subst A. exfalso. apply HA. apply in_or_app; right; apply in_or_app; right; simpl; auto.
    + exact E.
  - simpl in Hin; contradiction.
  - simpl in Hin; contradiction.
Qed.

Lemma fv_erase_tm : forall t, fv_tm (erase_tm t) = fv_tm t.
Proof. induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity. Qed.

Lemma lookup_update_eq : forall Gamma x A, lookup_context x (update Gamma x A) = Some A.
Proof. intros; simpl; rewrite Nat.eqb_refl; reflexivity. Qed.
Lemma lookup_update_neq : forall Gamma x y A,
  x <> y -> lookup_context y (update Gamma x A) = lookup_context y Gamma.
Proof. intros; simpl; assert (Nat.eqb y x = false) by (apply Nat.eqb_neq; congruence); rewrite H0; reflexivity. Qed.

Fixpoint context_fvars (G : context) : list atom :=
  match G with [] => [] | (_,A)::G' => ty_fvars A ++ context_fvars G' end.

Lemma context_fvars_lookup : forall G y A X,
  lookup_context y G = Some A -> In X (ty_fvars A) -> In X (context_fvars G).
Proof.
  induction G as [|[z B] G IH]; intros y A X Hlook Hx; simpl in *; [discriminate|].
  destruct (Nat.eqb y z) eqn:E.
  - inversion Hlook; subst; apply in_or_app; left; exact Hx.
  - apply in_or_app; right; eapply IH; eauto.
Qed.

Lemma interp_xi_update_fresh : forall T rho xi X P,
  ~ In X (ty_fvars T) -> forall z,
  (interp rho xi T z <-> interp rho (xi_update xi X P) T z).
Proof.
  intros T rho xi X P Hfresh z. apply interp_xi_irrel.
  intros Y HY z'. unfold xi_update. destruct (Nat.eqb Y X) eqn:E; [|tauto].
  apply Nat.eqb_eq in E; subst. exfalso; apply Hfresh; exact HY.
Qed.

Lemma SN_induction : forall t (P : tm -> Prop), strongly_normalizing t ->
  (forall t, (forall u, t --> u -> P u) -> P t) -> P t.
Proof.
  intros t P Hsn; induction Hsn as [t Hnext IH]; intros Hbody.
  apply Hbody; intros u Hu. apply IH with (u:=u); assumption.
Qed.

Lemma candidate_lc_sn : candidate (fun t => locally_closed_tm t /\ strongly_normalizing t).
Proof.
  constructor.
  - intros t [Hlc _]; exact Hlc.
  - intros t [_ Hsn]; exact Hsn.
  - intros t u [Hlc Hsn] Hstep; split; [eapply step_lc|eapply SN_step]; eauto.
  - intros t Hlc Hneutral Hred; split; [exact Hlc|].
    constructor; intros u Hstep; exact (proj2 (Hred u Hstep)).
Qed.

Lemma rho_ext_candidate : forall rho P,
  (forall i, candidate (rho i)) -> candidate P ->
  forall i, candidate (rho_ext rho P i).
Proof.
  intros rho P Hr Hp i; unfold rho_ext; destruct (Nat.eqb i 0); [exact Hp|].
  apply Hr.
Qed.

Lemma interp_candidate : forall T rho xi,
  (forall i, candidate (rho i)) ->
  (forall X, candidate (xi X)) ->
  candidate (interp rho xi T).
Proof.
  induction T; intros rho xi Hr Hx; simpl.
  - apply Hr.
  - apply Hx.
  - assert (HA : candidate (interp rho xi T1)) by (apply IHT1; assumption).
    assert (HB : candidate (interp rho xi T2)) by (apply IHT2; assumption).
    destruct HA as [HAlc HAsn HAstep HAne]; destruct HB as [HBlc HBsn HBstep HBne].
    constructor.
    + intros f Hf; exact (proj1 Hf).
    + intros f Hf; exact (proj1 (proj2 Hf)).
    + intros f f' Hf Hstep. destruct Hf as [Hflc [Hfsn Hfun]].
      split; [eapply step_lc; eassumption|].
      split; [eapply SN_step; eassumption|].
      intros a Ha. eapply HBstep.
      * apply Hfun; exact Ha.
      * apply ST_App1; [exact Hstep|apply HAlc; exact Ha].
    + intros f Hflc Hfn Hreds. split; [exact Hflc|]. split.
      * constructor; intros f' Hstep. exact (proj1 (proj2 (Hreds f' Hstep))).
      * intros a Ha.
        assert (Hgen : forall z, (forall u, z --> u ->
            (interp rho xi T1 u -> interp rho xi T2 (tm_app f u))) ->
            interp rho xi T1 z -> interp rho xi T2 (tm_app f z)).
        { intros z IHarg Hz. apply HBne.
          - unfold locally_closed_tm; apply lc_tm_app; [exact Hflc|apply HAlc; exact Hz].
          - simpl; exact I.
          - intros u Hu; inversion Hu; subst; simpl in Hfn; try contradiction.
            + destruct (Hreds _ H1) as [_ [_ Hfun']]. apply Hfun'; exact Hz.
            + eapply IHarg; [eassumption|]. eapply HAstep; eassumption. }
        pose proof (SN_induction a
          (fun z => interp rho xi T1 z -> interp rho xi T2 (tm_app f z))
          (HAsn a Ha) Hgen) as Hres.
        apply Hres; exact Ha.
  - assert (HB : forall P, candidate P -> candidate (interp (rho_ext rho P) xi T)).
    { intros P HP; apply IHT; [apply rho_ext_candidate; assumption|exact Hx]. }
    constructor.
    + intros f Hf; exact (proj1 Hf).
    + intros f Hf; exact (proj1 (proj2 Hf)).
    + intros f f' Hf Hstep. destruct Hf as [Hflc [Hsn Hall]].
      split; [eapply step_lc; eassumption|]. split.
      * eapply SN_step; eassumption.
      * intros P HP. specialize (Hall P HP).
        destruct (HB P HP) as [_ _ Hbody_step _].
        eapply Hbody_step; [exact Hall|].
        apply ST_TApp; [exact Hstep|constructor].
    + intros f Hflc Hfn Hreds. split; [exact Hflc|]. split.
      * constructor; intros f' Hstep. exact (proj1 (proj2 (Hreds f' Hstep))).
      * intros P HP. pose proof (HB P HP) as [HBlc HBsn HBstep HBne].
        apply HBne.
        -- unfold locally_closed_tm; apply lc_tm_tapp; [exact Hflc|constructor].
        -- simpl; exact I.
        -- intros u Hu. inversion Hu; subst; simpl in Hfn; try contradiction.
           exact (proj2 (proj2 (Hreds _ H1)) P HP).
  - apply candidate_lc_sn.
  - apply candidate_lc_sn.
Qed.

Lemma natrec_numeric : forall n, numeric_value n -> forall rho xi T b s,
  (forall i, candidate (rho i)) -> (forall X, candidate (xi X)) ->
  interp rho xi Ty_Nat n -> interp rho xi T b ->
  interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  interp rho xi T (tm_natrec n b s).
Proof.
  intros n Hnum; induction Hnum; intros rho xi T b s Hr Hxi Hn Hb Hs.
  - destruct (interp_candidate T rho xi Hr Hxi) as [Blc Bsn Bstep Bne].
    destruct (interp_candidate (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho xi Hr Hxi)
      as [Slc Ssn Sstep Sne].
    destruct (interp_candidate Ty_Nat rho xi Hr Hxi) as [Nlc Nsn Nstep Nne].
    assert (Hbound : interp rho xi T b -> forall ss,
        interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss -> interp rho xi T (tm_natrec tm_zero b ss)).
    { apply (SN_induction b
      (fun bb => interp rho xi T bb -> forall ss,
        interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss -> interp rho xi T (tm_natrec tm_zero bb ss))
      (Bsn b Hb)).
      intros bb Hbrec Hbb ss Hss.
      assert (Hssbound : interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss ->
        interp rho xi T (tm_natrec tm_zero bb ss)).
      { apply (SN_induction ss (fun ss' => interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss' ->
          interp rho xi T (tm_natrec tm_zero bb ss')) (Ssn ss Hss)).
        intros ss' Hssrec Hss'.
        apply Bne.
        - unfold locally_closed_tm; apply lc_tm_rec; [apply lc_tm_zero|exact (Blc _ Hbb)|exact (Slc _ Hss')].
        - simpl; exact I.
        - intros u Hu. inversion Hu; subst; try contradiction.
          + exfalso; inversion H2.
          + eapply Hbrec; [eassumption|eapply Bstep; eassumption|exact Hss'].
          + eapply Hssrec; [eassumption|eapply Sstep; eassumption].
          + exact Hbb. }
      exact (Hssbound Hss). }
    exact (Hbound Hb s Hs).
  - destruct (interp_candidate T rho xi Hr Hxi) as [Blc Bsn Bstep Bne].
    destruct (interp_candidate (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho xi Hr Hxi)
      as [Slc Ssn Sstep Sne].
    destruct (interp_candidate Ty_Nat rho xi Hr Hxi) as [Nlc Nsn Nstep Nne].
    assert (Hbound : interp rho xi T b -> forall ss,
        interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss -> interp rho xi T (tm_natrec (tm_succ n) b ss)).
    { apply (SN_induction b
      (fun bb => interp rho xi T bb -> forall ss,
        interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss -> interp rho xi T (tm_natrec (tm_succ n) bb ss))
      (Bsn b Hb)).
      intros bb Hbrec Hbb ss Hss.
      assert (Hssbound : interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss ->
        interp rho xi T (tm_natrec (tm_succ n) bb ss)).
      { apply (SN_induction ss (fun ss' => interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss' ->
          interp rho xi T (tm_natrec (tm_succ n) bb ss')) (Ssn ss Hss)).
        intros ss' Hssrec Hss'.
        apply Bne.
        - unfold locally_closed_tm; apply lc_tm_rec; [exact (Nlc _ Hn)|exact (Blc _ Hbb)|exact (Slc _ Hss')].
        - simpl; exact I.
        - intros u Hu. inversion Hu; subst; try contradiction.
          + exfalso. eapply value_no_step; [apply v_nat; constructor; exact Hnum|eassumption].
          + eapply Hbrec; [eassumption|eapply Bstep; eassumption|exact Hss'].
          + eapply Hssrec; [eassumption|eapply Sstep; eassumption].
          + assert (Hnm : interp rho xi Ty_Nat n).
            { split; [apply numeric_value_lc; exact Hnum|].
              apply SN_value; apply v_nat; exact Hnum. }
            assert (Hrec : interp rho xi T (tm_natrec n bb ss')).
            { eapply IHHnum; eauto using interp_candidate. }
            destruct Hss' as [Hslc [Hssn Hsfun]].
            destruct (Hsfun n Hnm) as [Hnfunlc [Hnfunsn Hnfun]].
            exact (Hnfun (tm_natrec n bb ss') Hrec). }
      exact (Hssbound Hss). }
    exact (Hbound Hb s Hs).
Qed.

Lemma natrec_reducible : forall rho xi T n b s,
  (forall i, candidate (rho i)) -> (forall X, candidate (xi X)) ->
  interp rho xi Ty_Nat n -> interp rho xi T b ->
  interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  interp rho xi T (tm_natrec n b s).
Proof.
  intros rho xi T n b s Hr Hxi Hn Hb Hs.
  destruct (interp_candidate Ty_Nat rho xi Hr Hxi) as [Nlc Nsn Nstep Nne].
  destruct (interp_candidate T rho xi Hr Hxi) as [Blc Bsn Bstep Bne].
  destruct (interp_candidate (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho xi Hr Hxi)
    as [Slc Ssn Sstep Sne].
  assert (Hbound : interp rho xi Ty_Nat n -> forall bb,
      interp rho xi T bb -> forall ss,
      interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss ->
      interp rho xi T (tm_natrec n bb ss)).
  { apply (SN_induction n
      (fun nn => interp rho xi Ty_Nat nn -> forall bb, interp rho xi T bb -> forall ss,
        interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss -> interp rho xi T (tm_natrec nn bb ss))
      (Nsn n Hn)).
    intros nn Hnrec Hnn bb Hbb ss Hss.
    assert (Hbbound : interp rho xi T bb -> forall ss',
      interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss' -> interp rho xi T (tm_natrec nn bb ss')).
    { apply (SN_induction bb
        (fun bb' => interp rho xi T bb' -> forall ss',
          interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss' -> interp rho xi T (tm_natrec nn bb' ss'))
        (Bsn bb Hbb)).
      intros bb' Hbrec Hb' ss' Hss'.
      assert (Hssbound : interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss' ->
        interp rho xi T (tm_natrec nn bb' ss')).
      { apply (SN_induction ss'
          (fun ss'' => interp rho xi (Ty_Arrow Ty_Nat (Ty_Arrow T T)) ss'' ->
             interp rho xi T (tm_natrec nn bb' ss'')) (Ssn ss' Hss')).
        intros ss'' Hssrec Hss''.
        apply Bne.
        - unfold locally_closed_tm; apply lc_tm_rec; [exact (Nlc _ Hnn)|exact (Blc _ Hb')|exact (Slc _ Hss'')].
        - simpl; exact I.
        - intros u Hu. inversion Hu; subst; try contradiction.
          + eapply Hnrec; [eassumption|eapply Nstep; eassumption|exact Hb'|exact Hss''].
          + eapply Hbrec; [eassumption|eapply Bstep; eassumption|exact Hss''].
          + eapply Hssrec; [eassumption|eapply Sstep; eassumption].
          + exact Hb'.
          + assert (Hnm : interp rho xi Ty_Nat n0).
            { split; [apply numeric_value_lc; exact H2|].
              apply SN_value; apply v_nat; exact H2. }
            assert (Hrec : interp rho xi T (tm_natrec n0 bb' ss'')).
            { eapply natrec_numeric; eauto. }
            destruct Hss'' as [_ [_ Hsf]].
            destruct (Hsf n0 Hnm) as [_ [_ Hsf']].
            exact (Hsf' (tm_natrec n0 bb' ss'') Hrec).
      }
      exact (Hssbound Hss').
    }
    exact (Hbbound Hbb ss Hss).
  }
  exact (Hbound Hn b Hb s Hs).
Qed.

Theorem fundamental : forall D G t T, has_type D G t T ->
  forall rho xi sigma,
    (forall i, candidate (rho i)) ->
    (forall X, candidate (xi X)) ->
    (forall x, locally_closed_tm (sigma x)) ->
    (forall y A, lookup_context y G = Some A -> interp rho xi A (sigma y)) ->
    interp rho xi T (subst_env sigma (erase_tm t)).
Proof.
  intros D G t T HT; induction HT; intros rho xi sigma Hr Hxi Hsig Hctx; simpl.
  - eapply Hctx; eauto.
  - assert (Hdom : candidate (interp rho xi T1)) by (apply interp_candidate; assumption).
    assert (Hcod : candidate (interp rho xi T2)) by (apply interp_candidate; assumption).
    destruct Hdom as [Hdomlc Hdomsn Hdomstep Hdomne].
    destruct Hcod as [Hcodlc Hcodsn Hcodstep Hcodne].
    assert (Hbodylc : lc_tm_at 0 1 (erase_tm t2)).
    { destruct (fresh_atom_notin (L ++ fv_tm t2)) as [x Hx].
      assert (Hxl : ~ In x L) by (intro E; apply Hx; apply in_or_app; left; exact E).
      pose proof (has_type_lc _ _ _ _ (H0 x Hxl)) as Hl.
      unfold locally_closed_tm, open_tm in Hl.
      apply erase_lc. eapply open_tm_lc_inverse with (K:=0) (k:=0) (u:=tm_fvar x).
      - unfold locally_closed_tm; constructor.
      - exact Hl. }
    assert (Hbody : lc_tm_at 0 1 (subst_env sigma (erase_tm t2))).
    { eapply subst_env_lc; [exact Hbodylc|exact Hsig]. }
    assert (HabsLC : locally_closed_tm (tm_abs Ty_Bool (subst_env sigma (erase_tm t2)))).
    { unfold locally_closed_tm; apply lc_tm_abs; [constructor|exact Hbody]. }
    split; [exact HabsLC|]. split.
    + apply SN_value. apply v_abs; exact HabsLC.
    + intros a Ha.
      assert (Hopen_forall : forall z, interp rho xi T1 z ->
        interp rho xi T2 (open_tm (subst_env sigma (erase_tm t2)) z)).
      { intros z Hz.
        destruct (fresh_atom_notin (L ++ fv_tm t2)) as [x Hx].
        assert (Hxl : ~ In x L) by (intro E; apply Hx; apply in_or_app; left; exact E).
        assert (Hxf : ~ In x (fv_tm (erase_tm t2))) by (rewrite fv_erase_tm; intro E; apply Hx; apply in_or_app; right; exact E).
        assert (Hsig' : forall y, locally_closed_tm (env_update sigma x z y)).
        { intro y; unfold env_update; destruct (Nat.eqb y x); [exact (Hdomlc _ Hz)|apply Hsig]. }
        assert (Hctx' : forall y A, lookup_context y (update Gamma x T1) = Some A ->
          interp rho xi A (env_update sigma x z y)).
        { intros y A Hy. destruct (Nat.eqb y x) eqn:E.
          - apply Nat.eqb_eq in E; subst. rewrite lookup_update_eq in Hy; inversion Hy; subst.
            unfold env_update; rewrite Nat.eqb_refl; exact Hz.
          - apply Nat.eqb_neq in E. rewrite lookup_update_neq in Hy by congruence.
            unfold env_update. assert (E' : Nat.eqb y x = false) by (apply Nat.eqb_neq; congruence).
            rewrite E'. eapply Hctx; eauto. }
        pose proof (H1 x Hxl rho xi (env_update sigma x z) Hr Hxi Hsig' Hctx') as Hrel.
        simpl in Hrel. rewrite erase_open_tm in Hrel. unfold open_tm in Hrel.
        change (interp rho xi T2 (subst_env (env_update sigma x z)
          (open_tm_rec 0 (tm_fvar x) (erase_tm t2)))) in Hrel.
        pose proof (subst_env_open (erase_tm t2) 0 x sigma z Hxf (Hdomlc z Hz) Hsig) as Heq.
        rewrite Heq in Hrel. exact Hrel. }
      apply (SN_induction a
        (fun z => interp rho xi T1 z -> interp rho xi T2
          (tm_app (tm_abs Ty_Bool (subst_env sigma (erase_tm t2))) z))
        (Hdomsn a Ha)).
      intros z Hrec Hz. apply Hcodne.
      * unfold locally_closed_tm; apply lc_tm_app; [exact HabsLC|apply Hdomlc; exact Hz].
      * simpl; exact I.
      * intros u Hu. inversion Hu; subst.
        -- exact (Hopen_forall z Hz).
        -- exfalso. eapply value_no_step; [apply v_abs; exact HabsLC|eassumption].
        -- apply Hrec; [eassumption|]. eapply Hdomstep; eassumption.
      * exact Ha.
  - pose proof (IHHT1 rho xi sigma Hr Hxi Hsig Hctx) as Hfun.
    pose proof (IHHT2 rho xi sigma Hr Hxi Hsig Hctx) as Harg.
    destruct Hfun as [Hflc [Hfsn Hff]].
    exact (Hff _ Harg).
  - (* type abstraction *)
    assert (HwfAll : wf_ty Delta (Ty_All T)) by (eapply has_type_wf; apply T_TAbs with (L:=L); exact H).
    pose proof (wf_ty_lc _ _ HwfAll) as HlcAll.
    assert (HlcT : lc_ty_at 1 T) by (inversion HlcAll; assumption).
    assert (Hbodylc : lc_tm_at 1 0 (erase_tm t)).
    { destruct (fresh_atom_notin L) as [X HX].
      pose proof (has_type_lc _ _ _ _ (H X HX)) as Hl.
      unfold locally_closed_tm, open_tm_ty in Hl.
      apply erase_lc. eapply open_tm_ty_lc_inverse; exact Hl. }
    assert (Hbody : lc_tm_at 1 0 (subst_env sigma (erase_tm t)))
      by (eapply subst_env_lc; [exact Hbodylc|exact Hsig]).
    assert (Hbodylc0 : lc_tm_at 0 0 (erase_tm t)).
    { destruct (fresh_atom_notin L) as [X HX].
      pose proof (has_type_lc _ _ _ _ (H X HX)) as Hl.
      unfold locally_closed_tm, open_tm_ty in Hl.
      pose proof (open_tm_ty_lc_inverse 0 0 X t Hl) as Hraw.
      eapply erase_lc_any; exact Hraw. }
    assert (Hbody0 : lc_tm_at 0 0 (subst_env sigma (erase_tm t)))
      by (eapply subst_env_lc; [exact Hbodylc0|exact Hsig]).
    assert (HtabsLC : locally_closed_tm (tm_tabs (subst_env sigma (erase_tm t))))
      by (unfold locally_closed_tm; apply lc_tm_tabs; exact Hbody).
    split; [exact HtabsLC|]. split.
    + apply SN_value. apply v_tabs; exact HtabsLC.
    + intros P HP.
      destruct (fresh_atom_notin (L ++ context_fvars Gamma ++ ty_fvars T)) as [X HX].
      assert (HXL : ~ In X L) by (intro E; apply HX; apply in_or_app; left; exact E).
      assert (HXctx : ~ In X (context_fvars Gamma)) by
        (intro E; apply HX; apply in_or_app; right; apply in_or_app; left; exact E).
      assert (HXT : ~ In X (ty_fvars T)) by
        (intro E; apply HX; apply in_or_app; right; apply in_or_app; right; exact E).
      set (xip := xi_update xi X P).
      assert (Hctxp : forall y A, lookup_context y Gamma = Some A -> interp rho xip A (sigma y)).
      { intros y A Hy. specialize (Hctx y A Hy).
        assert (Hnot : ~ In X (ty_fvars A)).
        { intro E. apply HXctx. eapply context_fvars_lookup; eauto. }
        apply (proj1 (interp_xi_update_fresh A rho xi X P Hnot (sigma y))); exact Hctx. }
      assert (Hxip : forall Y, candidate (xip Y)).
      { intro Y; unfold xip, xi_update. destruct (Nat.eqb Y X) eqn:E.
        - exact HP.
        - apply Hxi. }
      pose proof (H0 X HXL rho xip sigma Hr Hxip Hsig Hctxp) as Hrel.
      simpl in Hrel. rewrite erase_open_tm_ty in Hrel.
      assert (Hopen : locally_closed_ty (Ty_FVar X)) by constructor.
      pose proof (interp_open_ty T rho xip (Ty_FVar X) HlcT Hopen
        (subst_env sigma (erase_tm t))) as Hsem.
      assert (Hxpeq : xip X = P).
      { unfold xip, xi_update; rewrite Nat.eqb_refl; reflexivity. }
      apply (proj1 Hsem) in Hrel.
      assert (Hpeq : interp rho xip (Ty_FVar X) = P) by (change (xip X = P); exact Hxpeq).
      rewrite Hpeq in Hrel.
      assert (Hto : interp (rho_ext rho P) xip T (subst_env sigma (erase_tm t))).
      { exact Hrel. }
      assert (HxiT : forall Y, In Y (ty_fvars T) -> forall z,
        (xi_update xi X P) Y z <-> xi Y z).
      { intros Y HY z. unfold xi_update. destruct (Nat.eqb Y X) eqn:E; [|tauto].
        apply Nat.eqb_eq in E. exfalso; apply HXT. rewrite <- E; exact HY. }
      assert (HbodyP : interp (rho_ext rho P) xi T (subst_env sigma (erase_tm t))).
      { change (interp (rho_ext rho P) (xi_update xi X P) T (subst_env sigma (erase_tm t))) in Hto.
        exact (proj1 (interp_xi_irrel T (rho_ext rho P) (xi_update xi X P) xi HxiT
          (subst_env sigma (erase_tm t))) Hto). }
      clear Hrel Hsem Hxpeq Hpeq Hto Hxip Hctxp HxiT.
      assert (HcandT : candidate (interp (rho_ext rho P) xi T))
        by (apply interp_candidate; [apply rho_ext_candidate; assumption|exact Hxi]).
      destruct HcandT as [Htlc Htsn Htstep Htneutral].
      apply Htneutral.
      * unfold locally_closed_tm; apply lc_tm_tapp; [exact HtabsLC|constructor].
      * simpl; exact I.
      * intros u Hu. inversion Hu; subst.
        -- unfold open_tm_ty. rewrite open_tm_ty_lc_id with (K:=0) (k:=0)
             (t:=subst_env sigma (erase_tm t)) (U:=Ty_Bool) by (try lia; exact Hbody0).
           exact HbodyP.
        -- exfalso. eapply value_no_step; [apply v_tabs; exact HtabsLC|eassumption].
  - (* type application *)
    pose proof (IHHT rho xi sigma Hr Hxi Hsig Hctx) as Hpoly.
    destruct Hpoly as [Hflc [Hfsn Hall]].
    pose proof (has_type_wf _ _ _ _ HT) as HwfAll.
    pose proof (wf_ty_lc _ _ HwfAll) as HlcAll.
    assert (HlcT : lc_ty_at 1 T) by (inversion HlcAll; assumption).
    pose proof (wf_ty_lc _ _ H) as HlcU.
    apply (proj2 (interp_open_ty T rho xi U HlcT HlcU
      (tm_tapp (subst_env sigma (erase_tm t)) Ty_Bool))).
    apply Hall.
    apply interp_candidate; assumption.
  - split; [unfold locally_closed_tm; constructor|]. apply SN_value; apply v_true.
  - split; [unfold locally_closed_tm; constructor|]. apply SN_value; apply v_false.
  - pose proof (IHHT1 rho xi sigma Hr Hxi Hsig Hctx) as Hc.
    pose proof (IHHT2 rho xi sigma Hr Hxi Hsig Hctx) as Ha.
    pose proof (IHHT3 rho xi sigma Hr Hxi Hsig Hctx) as Hb.
    destruct (interp_candidate T rho xi Hr Hxi) as [HTlc HTsn HTstep HTne].
    destruct (interp_candidate Ty_Bool rho xi Hr Hxi) as [_ _ Hboolstep _].
    apply (SN_induction (subst_env sigma (erase_tm t1))
      (fun c => interp rho xi Ty_Bool c -> interp rho xi T
        (tm_if c (subst_env sigma (erase_tm t2)) (subst_env sigma (erase_tm t3))))
      (proj2 Hc)).
    + intros c Hrec Hcb. apply HTne.
      * unfold locally_closed_tm; apply lc_tm_if.
        -- exact (proj1 Hcb).
        -- exact (HTlc _ Ha).
        -- exact (HTlc _ Hb).
      * simpl; exact I.
      * intros u Hu. inversion Hu; subst.
        -- exact Ha.
        -- exact Hb.
        -- apply (Hrec _ H2). eapply Hboolstep; eassumption.
    + exact Hc.
  - split; [unfold locally_closed_tm; constructor|]. apply SN_value; apply v_nat; constructor.
  - pose proof (IHHT rho xi sigma Hr Hxi Hsig Hctx) as Hn.
    split; [unfold locally_closed_tm; apply lc_tm_succ; exact (proj1 Hn)|].
    apply (SN_induction (subst_env sigma (erase_tm n))
      (fun z => strongly_normalizing (tm_succ z)) (proj2 Hn)).
    intros z Hrec. constructor. intros u Hu. inversion Hu; subst. apply Hrec; assumption.
  - pose proof (IHHT1 rho xi sigma Hr Hxi Hsig Hctx) as Hn.
    pose proof (IHHT2 rho xi sigma Hr Hxi Hsig Hctx) as Hb.
    pose proof (IHHT3 rho xi sigma Hr Hxi Hsig Hctx) as Hs.
    eapply natrec_reducible; eassumption.
Qed.

Lemma SN_erase_back : forall t, strongly_normalizing (erase_tm t) -> strongly_normalizing t.
Proof.
  intros t Hsn.
  eapply (SN_induction (erase_tm t) (fun e => forall s, erase_tm s = e -> strongly_normalizing s) Hsn).
  intros e Hred s Heq. constructor. intros u Hu.
  apply (Hred (erase_tm u)).
  - rewrite <- Heq; apply step_erase; exact Hu.
  - reflexivity.
  - reflexivity.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T HT.
  set (C := fun z => locally_closed_tm z /\ strongly_normalizing z).
  assert (Hcand : candidate C) by apply candidate_lc_sn.
  assert (Hctx0 : forall y A, lookup_context y empty = Some A -> interp (fun _ => C) (fun _ => C) A (tm_fvar y)).
  { intros y A Hlook. simpl in Hlook; discriminate. }
  pose proof (fundamental _ _ _ _ HT (fun _ => C) (fun _ => C) (fun x => tm_fvar x)
    (fun _ => Hcand) (fun _ => Hcand)
    (fun x => ltac:(unfold locally_closed_tm; constructor)) Hctx0) as Hfund.
  change (interp (fun _ => C) (fun _ => C) T
    (subst_env (fun x => tm_fvar x) (erase_tm t))) in Hfund.
  rewrite subst_env_identity in Hfund.
  assert (HsnE : strongly_normalizing (erase_tm t)).
  { pose proof (interp_candidate T (fun _ => C) (fun _ => C)
      (fun _ => Hcand) (fun _ => Hcand)) as HTcand.
    destruct HTcand as [_ Htsn _ _]. exact (Htsn _ Hfund). }
  apply SN_erase_back; exact HsnE.
Qed.

End SystemFNormalizationIfRecursionHardTask.
