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

(* Construct the logical relation and supporting proofs here. *)

Definition candidate := tm -> Prop.

Fixpoint realizes (T : ty) (rho : list candidate)
    (eta : atom -> candidate) (v : tm) {struct T} : Prop :=
  value v /\
  match T with
  | Ty_BVar i => nth i rho (fun _ => False) v
  | Ty_FVar X => eta X v
  | Ty_Arrow A B =>
      match v with
      | tm_abs _ body =>
          forall w, realizes A rho eta w ->
            exists z, multi (open_tm body w) z /\ realizes B rho eta z
      | _ => False
      end
  | Ty_All A =>
      match v with
      | tm_tabs body =>
          forall U (Q : candidate), locally_closed_ty U ->
            (forall w, Q w -> value w) ->
            exists z, multi (open_tm_ty body U) z /\
              realizes A (Q :: rho) eta z
      | _ => False
      end
  | Ty_Bool => v = tm_true \/ v = tm_false
  | Ty_Nat => numeric_value v
  end.

Definition reducible (T : ty) (rho : list candidate)
    (eta : atom -> candidate) (t : tm) : Prop :=
  exists v, multi t v /\ realizes T rho eta v.

Lemma realizes_value : forall T rho eta v,
  realizes T rho eta v -> value v.
Proof. intros T rho eta v H; destruct T; exact (proj1 H). Qed.

Lemma numeric_value_no_step : forall n u,
  numeric_value n -> ~ step n u.
Proof.
  intros n u Hn; revert u; induction Hn; intros u Hs; inversion Hs; subst;
    eauto.
  eapply IHHn; eauto.
Qed.

Lemma value_no_step : forall v u, value v -> ~ step v u.
Proof.
  intros v u Hv Hs; destruct Hv.
  - inversion Hs.
  - inversion Hs.
  - inversion Hs.
  - inversion Hs.
  - eapply numeric_value_no_step; eauto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; destruct H as [T t Hlc | t Hlc | | | n Hnv];
    try assumption; try (unfold locally_closed_tm; constructor).
  induction Hnv; unfold locally_closed_tm in *; eauto.
Qed.

Lemma numeric_value_numeral : forall v,
  numeric_value v -> exists n, v = numeral n.
Proof.
  intros v H; induction H as [|v Hv [n ->]].
  - exists 0; reflexivity.
  - exists (S n); reflexivity.
Qed.

Lemma multi_trans : forall a b c, multi a b -> multi b c -> multi a c.
Proof.
  intros a b c H; induction H; eauto using multi.
Qed.

Lemma multi_one : forall a b, step a b -> multi a b.
Proof. eauto using multi. Qed.

Lemma reducible_step_back : forall T rho eta a b,
  step a b -> reducible T rho eta b -> reducible T rho eta a.
Proof.
  intros T rho eta a b Hab [v [Hb Hv]].
  exists v; split; eauto using multi.
Qed.

Lemma multi_app1 : forall a a' b, multi a a' ->
  locally_closed_tm b -> multi (tm_app a b) (tm_app a' b).
Proof.
  intros a a' b H; induction H; intros Hb; eauto using multi, step.
Qed.

Lemma multi_app2 : forall v b b', value v -> multi b b' ->
  multi (tm_app v b) (tm_app v b').
Proof.
  intros v b b' Hv H; induction H; eauto using multi, step.
Qed.

Lemma multi_tapp : forall a a' U, multi a a' ->
  locally_closed_ty U -> multi (tm_tapp a U) (tm_tapp a' U).
Proof.
  intros a a' U H; induction H; intros HU; eauto using multi, step.
Qed.

Lemma multi_succ : forall a a', multi a a' ->
  multi (tm_succ a) (tm_succ a').
Proof. intros a a' H; induction H; eauto using multi, step. Qed.

Lemma multi_if : forall a a' b c, multi a a' ->
  locally_closed_tm b -> locally_closed_tm c ->
  multi (tm_if a b c) (tm_if a' b c).
Proof.
  intros a a' b c H; induction H; intros Hb Hc; eauto using multi, step.
Qed.

Lemma multi_rec_arg : forall a a' b s, multi a a' ->
  locally_closed_tm b -> locally_closed_tm s ->
  multi (tm_natrec a b s) (tm_natrec a' b s).
Proof.
  intros a a' b s H; induction H; intros Hb Hs; eauto using multi, step.
Qed.

Lemma multi_rec_base : forall n b b' s, numeric_value n ->
  multi b b' -> locally_closed_tm s ->
  multi (tm_natrec n b s) (tm_natrec n b' s).
Proof.
  intros n b b' s Hn H; induction H; intros Hs; eauto using multi, step.
Qed.

Lemma multi_rec_step : forall n b s s', numeric_value n -> value b ->
  multi s s' -> multi (tm_natrec n b s) (tm_natrec n b s').
Proof.
  intros n b s s' Hn Hb H; induction H; eauto using multi, step.
Qed.

Lemma fresh_list : forall L : list atom, exists x, ~ In x L.
Proof.
  intros L; assert (B : forall y, In y L ->
    y <= fold_right Nat.max 0 L).
  { induction L as [|a L IH]; intros y Hy; simpl in *; [contradiction|].
    destruct Hy as [->|Hy].
    - apply Nat.le_max_l.
    - eapply Nat.le_trans; [apply IH; exact Hy|apply Nat.le_max_r]. }
  exists (S (fold_right Nat.max 0 L)); intros H.
  specialize (B _ H); lia.
Qed.

Lemma lc_ty_open_inv : forall T k X,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) ->
  lc_ty_at (S k) T.
Proof.
  induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_open_inv : forall t K k x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
  lc_tm_at K (S k) t.
Proof.
  induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; constructor; lia.
    + inversion H; subst; constructor; lia.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma lc_tm_ty_open_inv : forall t K k X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) ->
  lc_tm_at (S K) k t.
Proof.
  induction t; intros K k X H; simpl in H.
  - inversion H; subst; constructor; lia.
  - constructor.
  - inversion H; subst; constructor.
    + eapply lc_ty_open_inv; eassumption.
    + eapply IHt; eassumption.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor.
    + eapply IHt; eassumption.
    + eapply lc_ty_open_inv; eassumption.
  - constructor.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - constructor.
  - inversion H; subst; constructor; eauto.
  - inversion H; subst; constructor; eauto.
Qed.

Lemma wf_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T H; induction H; unfold locally_closed_ty in *;
    eauto using lc_ty_at.
  destruct (fresh_list L) as [X HX].
  apply lc_ty_all.
  eapply lc_ty_open_inv; exact (H0 X HX).
Qed.

Lemma typing_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H; induction H;
    unfold locally_closed_tm in *; eauto using lc_tm_at, wf_lc.
  - destruct (fresh_list L) as [x Hx].
    apply lc_tm_abs; [eapply wf_lc; eassumption|].
    eapply lc_tm_open_inv; exact (H1 x Hx).
  - destruct (fresh_list L) as [X HX].
    apply lc_tm_tabs.
    eapply lc_tm_ty_open_inv; exact (H0 X HX).
  - apply lc_tm_tapp; [assumption|eapply wf_lc; eassumption].
Qed.

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_FVar X => [X]
  | Ty_Arrow A B => fv_ty A ++ fv_ty B
  | Ty_All A => fv_ty A
  | _ => []
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_fvar x => [x]
  | tm_abs _ b | tm_tabs b | tm_tapp b _ | tm_succ b => fv_tm b
  | tm_app a b => fv_tm a ++ fv_tm b
  | tm_if a b c | tm_natrec a b c => fv_tm a ++ fv_tm b ++ fv_tm c
  | _ => []
  end.

Fixpoint fv_tm_ty (t : tm) : list atom :=
  match t with
  | tm_abs T b => fv_ty T ++ fv_tm_ty b
  | tm_tabs b | tm_succ b => fv_tm_ty b
  | tm_tapp b T => fv_tm_ty b ++ fv_ty T
  | tm_app a b => fv_tm_ty a ++ fv_tm_ty b
  | tm_if a b c | tm_natrec a b c =>
      fv_tm_ty a ++ fv_tm_ty b ++ fv_tm_ty c
  | _ => []
  end.

Fixpoint fv_gamma_ty (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_,T)::Gamma' => fv_ty T ++ fv_gamma_ty Gamma'
  end.

Fixpoint dom_gamma (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (x,_)::Gamma' => x :: dom_gamma Gamma'
  end.

Fixpoint map_ty (theta : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => theta X
  | Ty_Arrow A B => Ty_Arrow (map_ty theta A) (map_ty theta B)
  | Ty_All A => Ty_All (map_ty theta A)
  | Ty_Bool => Ty_Bool
  | Ty_Nat => Ty_Nat
  end.

Fixpoint map_tm_ty (theta : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (map_ty theta T) (map_tm_ty theta b)
  | tm_app a b => tm_app (map_tm_ty theta a) (map_tm_ty theta b)
  | tm_tabs b => tm_tabs (map_tm_ty theta b)
  | tm_tapp a T => tm_tapp (map_tm_ty theta a) (map_ty theta T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if a b c => tm_if (map_tm_ty theta a) (map_tm_ty theta b)
                            (map_tm_ty theta c)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (map_tm_ty theta a)
  | tm_natrec a b c => tm_natrec (map_tm_ty theta a) (map_tm_ty theta b)
                                    (map_tm_ty theta c)
  end.

Fixpoint map_tm (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T b => tm_abs T (map_tm sigma b)
  | tm_app a b => tm_app (map_tm sigma a) (map_tm sigma b)
  | tm_tabs b => tm_tabs (map_tm sigma b)
  | tm_tapp a T => tm_tapp (map_tm sigma a) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if a b c => tm_if (map_tm sigma a) (map_tm sigma b) (map_tm sigma c)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (map_tm sigma a)
  | tm_natrec a b c => tm_natrec (map_tm sigma a) (map_tm sigma b)
                                  (map_tm sigma c)
  end.

Definition close_tm (theta : atom -> ty) (sigma : atom -> tm) (t : tm) :=
  map_tm sigma (map_tm_ty theta t).

Lemma map_ty_ext : forall T a b,
  (forall X, In X (fv_ty T) -> a X = b X) ->
  map_ty a T = map_ty b T.
Proof.
  intros T a b; induction T; simpl in *; intros H; try reflexivity.
  - apply H; simpl; auto.
  - f_equal; [apply IHT1|apply IHT2]; intros X HX;
      apply H; apply in_or_app; auto.
  - f_equal; apply IHT; assumption.
Qed.

Lemma map_tm_ext : forall t a b,
  (forall x, In x (fv_tm t) -> a x = b x) ->
  map_tm a t = map_tm b t.
Proof.
  intros t a b; induction t; simpl in *; intros H; try reflexivity.
  - apply H; simpl; auto.
  - f_equal; apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2]; intros x Hx;
      apply H; apply in_or_app; auto.
  - f_equal; apply IHt; assumption.
  - f_equal; apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; intros x Hx;
      apply H; simpl; repeat rewrite in_app_iff; tauto.
  - f_equal; apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; intros x Hx;
      apply H; simpl; repeat rewrite in_app_iff; tauto.
Qed.

Lemma map_tm_ty_ext : forall t a b,
  (forall X, In X (fv_tm_ty t) -> a X = b X) ->
  map_tm_ty a t = map_tm_ty b t.
Proof.
  intros t a b; induction t; simpl in *; intros H; try reflexivity.
  - f_equal.
    + apply map_ty_ext; intros X HX; apply H; apply in_or_app; auto.
    + apply IHt; intros X HX; apply H; apply in_or_app; auto.
  - f_equal; [apply IHt1|apply IHt2]; intros X HX;
      apply H; apply in_or_app; auto.
  - f_equal; apply IHt; assumption.
  - f_equal.
    + apply IHt; intros X HX; apply H; apply in_or_app; auto.
    + apply map_ty_ext; intros X HX; apply H; apply in_or_app; auto.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; intros X HX;
      apply H; simpl; repeat rewrite in_app_iff; tauto.
  - f_equal; apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; intros X HX;
      apply H; simpl; repeat rewrite in_app_iff; tauto.
Qed.

Lemma lc_ty_weaken : forall k T, lc_ty_at k T ->
  forall j, k <= j -> lc_ty_at j T.
Proof.
  intros k T H; induction H; intros j Hj.
  - apply lc_ty_bvar; lia.
  - constructor.
  - apply lc_ty_arrow; eauto.
  - apply lc_ty_all; apply IHlc_ty_at; lia.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_weaken : forall K k t, lc_tm_at K k t ->
  forall J j, K <= J -> k <= j -> lc_tm_at J j t.
Proof.
  intros K k t H; induction H; intros J j HJ Hj.
  - apply lc_tm_bvar; lia.
  - constructor.
  - apply lc_tm_abs.
    + eapply lc_ty_weaken; eauto.
    + apply IHlc_tm_at; lia.
  - apply lc_tm_app; eauto.
  - apply lc_tm_tabs; apply IHlc_tm_at; lia.
  - apply lc_tm_tapp; eauto using lc_ty_weaken.
  - constructor.
  - constructor.
  - apply lc_tm_if; eauto.
  - constructor.
  - apply lc_tm_succ; eauto.
  - apply lc_tm_rec; eauto.
Qed.

Lemma map_ty_lc : forall k T theta,
  lc_ty_at k T ->
  (forall X, locally_closed_ty (theta X)) ->
  lc_ty_at k (map_ty theta T).
Proof.
  intros k T theta H; induction H; intros Htheta; simpl;
    try (constructor; eauto; fail).
  eapply lc_ty_weaken; [apply Htheta|lia].
Qed.

Lemma map_tm_ty_lc : forall K k t theta,
  lc_tm_at K k t ->
  (forall X, locally_closed_ty (theta X)) ->
  lc_tm_at K k (map_tm_ty theta t).
Proof.
  intros K k t theta H; induction H; intros Htheta; simpl;
    try (constructor; eauto using map_ty_lc; fail).
Qed.

Lemma map_tm_lc : forall K k t sigma,
  lc_tm_at K k t ->
  (forall x, locally_closed_tm (sigma x)) ->
  lc_tm_at K k (map_tm sigma t).
Proof.
  intros K k t sigma H; induction H; intros Hsigma; simpl;
    try (constructor; eauto; fail).
  eapply lc_tm_weaken; [apply Hsigma|lia|lia].
Qed.

Lemma close_tm_lc : forall theta sigma t,
  locally_closed_tm t ->
  (forall X, locally_closed_ty (theta X)) ->
  (forall x, locally_closed_tm (sigma x)) ->
  locally_closed_tm (close_tm theta sigma t).
Proof.
  intros theta sigma t Ht Htheta Hsigma.
  unfold close_tm; eapply map_tm_lc; eauto using map_tm_ty_lc.
Qed.

Lemma lc_ty_open_id : forall k T, lc_ty_at k T ->
  forall j U, k <= j -> open_ty_rec j U T = T.
Proof.
  intros k T H; induction H; intros j U Hj; simpl;
    try (f_equal; eauto; fail); try reflexivity.
  - destruct (j =? i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal; eapply IHlc_ty_at; lia.
Qed.

Lemma lc_tm_open_id : forall K k t, lc_tm_at K k t ->
  forall j u, k <= j -> open_tm_rec j u t = t.
Proof.
  intros K k t H; induction H; intros j u Hj; simpl;
    try (f_equal; eauto; fail); try reflexivity.
  - destruct (j =? i) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
  - f_equal; eapply IHlc_tm_at; lia.
Qed.

Lemma lc_tm_ty_open_id : forall K k t, lc_tm_at K k t ->
  forall J U, K <= J -> open_tm_ty_rec J U t = t.
Proof.
  intros K k t H; induction H; intros J U HJ; simpl;
    try reflexivity.
  - f_equal.
    + eapply lc_ty_open_id; eauto.
    + eapply IHlc_tm_at; lia.
  - f_equal; eauto.
  - f_equal; eapply IHlc_tm_at; lia.
  - f_equal.
    + eapply IHlc_tm_at; lia.
    + eapply lc_ty_open_id; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma map_ty_open : forall T k X theta,
  (forall Y, locally_closed_ty (theta Y)) ->
  map_ty theta (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k (theta X) (map_ty theta T).
Proof.
  induction T; intros k X theta Htheta; simpl;
    try reflexivity.
  - destruct (k =? n); reflexivity.
  - symmetry; eapply lc_ty_open_id; [apply Htheta|lia].
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma map_tm_ty_open_tm : forall t k x theta,
  map_tm_ty theta (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (tm_fvar x) (map_tm_ty theta t).
Proof.
  induction t; intros k x theta; simpl; try reflexivity;
    try (f_equal; eauto; fail).
  destruct (k =? n); reflexivity.
Qed.

Lemma map_tm_open : forall t k x sigma,
  (forall y, locally_closed_tm (sigma y)) ->
  map_tm sigma (open_tm_rec k (tm_fvar x) t) =
  open_tm_rec k (sigma x) (map_tm sigma t).
Proof.
  induction t; intros k x sigma Hsigma; simpl; try reflexivity.
  - destruct (k =? n); reflexivity.
  - symmetry; eapply lc_tm_open_id; [apply Hsigma|lia].
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma map_tm_ty_open_ty : forall t K X theta,
  (forall Y, locally_closed_ty (theta Y)) ->
  map_tm_ty theta (open_tm_ty_rec K (Ty_FVar X) t) =
  open_tm_ty_rec K (theta X) (map_tm_ty theta t).
Proof.
  induction t; intros K X theta Htheta; simpl; try reflexivity.
  - f_equal.
    + apply map_ty_open; assumption.
    + apply IHt; assumption.
  - f_equal; eauto.
  - f_equal; apply IHt; assumption.
  - f_equal.
    + apply IHt; assumption.
    + apply map_ty_open; assumption.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma map_tm_open_ty : forall t K U sigma,
  (forall x, locally_closed_tm (sigma x)) ->
  map_tm sigma (open_tm_ty_rec K U t) =
  open_tm_ty_rec K U (map_tm sigma t).
Proof.
  induction t; intros K U sigma Hsigma; simpl; try reflexivity.
  - symmetry; eapply lc_tm_ty_open_id; [apply Hsigma|lia].
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Definition cand_equiv (P Q : candidate) : Prop :=
  forall v, P v <-> Q v.

Definition rho_equiv (r1 r2 : list candidate) : Prop :=
  forall i, cand_equiv (nth i r1 (fun _ => False))
                         (nth i r2 (fun _ => False)).

Lemma realizes_ext : forall T r1 r2 e1 e2 v,
  rho_equiv r1 r2 ->
  (forall X, In X (fv_ty T) -> cand_equiv (e1 X) (e2 X)) ->
  (realizes T r1 e1 v <-> realizes T r2 e2 v).
Proof.
  induction T; intros r1 r2 e1 e2 v Hr He; simpl in *.
  - destruct (Hr n v) as [Hf Hb]; split; intros [Hv H]; split; auto.
  - destruct (He a (or_introl eq_refl) v) as [Hf Hb];
      split; intros [Hv H]; split; auto.
  - destruct v; try tauto.
    assert (E1 : forall X, In X (fv_ty T1) -> cand_equiv (e1 X) (e2 X)).
    { intros X HX; apply He; apply in_or_app; auto. }
    assert (E2 : forall X, In X (fv_ty T2) -> cand_equiv (e1 X) (e2 X)).
    { intros X HX; apply He; apply in_or_app; auto. }
    split; intros [Hv Hfn]; split; auto; intros w Hw.
    + apply (proj2 (IHT1 _ _ _ _ w Hr E1)) in Hw.
      destruct (Hfn w Hw) as [z [Hred Hz]].
      exists z; split; auto.
      apply (proj1 (IHT2 _ _ _ _ z Hr E2)); auto.
    + apply (proj1 (IHT1 _ _ _ _ w Hr E1)) in Hw.
      destruct (Hfn w Hw) as [z [Hred Hz]].
      exists z; split; auto.
      apply (proj2 (IHT2 _ _ _ _ z Hr E2)); auto.
  - destruct v; try tauto.
    assert (Hr' : forall Q, rho_equiv (Q::r1) (Q::r2)).
    { intros Q [|i]; simpl; [unfold cand_equiv; tauto|apply Hr]. }
    split; intros [Hv Hfn]; split; auto; intros U Q HU HQ.
    + destruct (Hfn U Q HU HQ) as [z [Hred Hz]].
      exists z; split; auto.
      apply (proj1 (IHT (Q::r1) (Q::r2) e1 e2 z (Hr' Q) He)); auto.
    + destruct (Hfn U Q HU HQ) as [z [Hred Hz]].
      exists z; split; auto.
      apply (proj2 (IHT (Q::r1) (Q::r2) e1 e2 z (Hr' Q) He)); auto.
  - tauto.
  - tauto.
Qed.

Definition rho_equiv_upto (k : nat) (r1 r2 : list candidate) : Prop :=
  forall i, i < k ->
    cand_equiv (nth i r1 (fun _ => False))
               (nth i r2 (fun _ => False)).

Lemma realizes_lc_env : forall k T, lc_ty_at k T ->
  forall r1 r2 eta v,
  rho_equiv_upto k r1 r2 ->
  (realizes T r1 eta v <-> realizes T r2 eta v).
Proof.
  intros k T H; induction H; intros r1 r2 eta v Hr; simpl.
  - destruct (Hr i H v) as [Hf Hb]; split; intros [Hv Hq]; split; auto.
  - tauto.
  - destruct v; try tauto.
    split; intros [Hv Hfn]; split; auto; intros w Hw.
    + apply (proj2 (IHlc_ty_at1 r1 r2 eta w Hr)) in Hw.
      destruct (Hfn w Hw) as [z [Hm Hz]].
      exists z; split; auto.
      apply (proj1 (IHlc_ty_at2 r1 r2 eta z Hr)); auto.
    + apply (proj1 (IHlc_ty_at1 r1 r2 eta w Hr)) in Hw.
      destruct (Hfn w Hw) as [z [Hm Hz]].
      exists z; split; auto.
      apply (proj2 (IHlc_ty_at2 r1 r2 eta z Hr)); auto.
  - destruct v; try tauto.
    assert (Hr' : forall Q, rho_equiv_upto (S k) (Q::r1) (Q::r2)).
    { intros Q [|i] Hi; simpl.
      - unfold cand_equiv; tauto.
      - apply Hr; lia. }
    split; intros [Hv Hfn]; split; auto; intros U Q HU HQ.
    + destruct (Hfn U Q HU HQ) as [z [Hm Hz]].
      exists z; split; auto.
      apply (proj1 (IHlc_ty_at (Q::r1) (Q::r2) eta z (Hr' Q))); auto.
    + destruct (Hfn U Q HU HQ) as [z [Hm Hz]].
      exists z; split; auto.
      apply (proj2 (IHlc_ty_at (Q::r1) (Q::r2) eta z (Hr' Q))); auto.
  - tauto.
  - tauto.
Qed.

Lemma realizes_open_ty : forall T k U eta prefix suffix v,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  length prefix = k ->
  (realizes (open_ty_rec k U T) (prefix ++ suffix) eta v <->
   realizes T (prefix ++ realizes U [] eta :: suffix) eta v).
Proof.
  induction T; intros k U eta prefix suffix v HT HU Hp;
    simpl in *.
  - inversion HT; subst; rename H1 into Hi.
    destruct (Nat.eqb (length prefix) n) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      rewrite nth_middle.
      assert (Er : realizes U (prefix ++ suffix) eta v <->
                   realizes U [] eta v).
      { eapply realizes_lc_env; eauto.
        intros i Hlt; lia. }
      split; intros Hq.
      * split; [eapply realizes_value; eauto|apply Er; exact Hq].
      * apply Er; exact (proj2 Hq).
    + apply Nat.eqb_neq in E.
      assert (n < length prefix) by lia.
      simpl; rewrite !app_nth1 by lia.
      tauto.
  - tauto.
  - inversion HT; subst.
    destruct v; try tauto.
    split; intros [Hv Hfn]; split; auto; intros w Hw.
    + apply (proj2 (IHT1 (length prefix) U eta prefix suffix w H2 HU eq_refl)) in Hw.
      destruct (Hfn w Hw) as [z [Hm Hz]].
      exists z; split; auto.
      apply (proj1 (IHT2 (length prefix) U eta prefix suffix z H3 HU eq_refl)); auto.
    + apply (proj1 (IHT1 (length prefix) U eta prefix suffix w H2 HU eq_refl)) in Hw.
      destruct (Hfn w Hw) as [z [Hm Hz]].
      exists z; split; auto.
      apply (proj2 (IHT2 (length prefix) U eta prefix suffix z H3 HU eq_refl)); auto.
  - inversion HT; subst.
    destruct v; try tauto.
    split; intros [Hv Hfn]; split; auto; intros W Q HW HQ.
    + destruct (Hfn W Q HW HQ) as [z [Hm Hz]].
      exists z; split; auto.
      apply (proj1 (IHT (S (length prefix)) U eta (Q::prefix) suffix z H1 HU eq_refl));
        simpl; auto.
    + destruct (Hfn W Q HW HQ) as [z [Hm Hz]].
      exists z; split; auto.
      apply (proj2 (IHT (S (length prefix)) U eta (Q::prefix) suffix z H1 HU eq_refl));
        simpl; auto.
  - tauto.
  - tauto.
Qed.

Lemma lc_ty_open_preserve : forall T k U,
  lc_ty_at (S k) T -> locally_closed_ty U ->
  lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; simpl.
  - inversion HT; subst.
    destruct (k =? n) eqn:E.
    + eapply lc_ty_weaken; [apply HU|lia].
    + apply Nat.eqb_neq in E; constructor; lia.
  - constructor.
  - inversion HT; subst; constructor; eauto.
  - inversion HT; subst; constructor; eauto.
  - constructor.
  - constructor.
Qed.

Lemma typing_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_ty T.
Proof.
  intros Delta Gamma t T H; induction H;
    unfold locally_closed_ty in *.
  - eapply wf_lc; eassumption.
  - apply lc_ty_arrow.
    + eapply wf_lc; eassumption.
    + destruct (fresh_list L) as [x Hx]; exact (H1 x Hx).
  - inversion IHhas_type1; subst; assumption.
  - destruct (fresh_list L) as [X HX].
    apply lc_ty_all; eapply lc_ty_open_inv; exact (H0 X HX).
  - inversion IHhas_type; subst.
    eapply lc_ty_open_preserve; eauto using wf_lc.
  - constructor.
  - constructor.
  - exact IHhas_type2.
  - constructor.
  - constructor.
  - exact IHhas_type2.
Qed.

Lemma realizes_nat : forall rho eta n,
  numeric_value n -> realizes Ty_Nat rho eta n.
Proof.
  intros rho eta n Hn; simpl; split; auto using value.
Qed.

Lemma reducible_app : forall A B rho eta f a,
  reducible (Ty_Arrow A B) rho eta f ->
  reducible A rho eta a ->
  locally_closed_tm a ->
  reducible B rho eta (tm_app f a).
Proof.
  intros A B rho eta f a [vf [Hf Hfv]] [va [Ha Hav]] Hlc.
  destruct vf; try (destruct Hfv as [_ Hbad]; contradiction).
  destruct Hfv as [Hv Hfun].
  destruct (Hfun va Hav) as [z [Hbody Hz]].
  exists z; split; auto.
  eapply multi_trans; [apply multi_app1; eauto|].
  eapply multi_trans; [apply multi_app2; eauto using realizes_value|].
  eapply multi_trans.
  - eapply multi_one; apply ST_AppAbs.
    + apply value_lc; exact Hv.
    + eapply realizes_value; eauto.
  - exact Hbody.
Qed.

Lemma reducible_tapp : forall A rho eta t U Q,
  reducible (Ty_All A) rho eta t ->
  locally_closed_ty U ->
  (forall v, Q v -> value v) ->
  reducible A (Q::rho) eta (tm_tapp t U).
Proof.
  intros A rho eta t U Q [v [Hm Hreal]] HU HQ.
  destruct v; try (destruct Hreal as [_ Hbad]; contradiction).
  destruct Hreal as [Hv Hfun].
  destruct (Hfun U Q HU HQ) as [z [Hb Hz]].
  exists z; split; auto.
  eapply multi_trans; [apply multi_tapp; eauto|].
  eapply multi_trans.
  - eapply multi_one; apply ST_TAppTabs; auto using value_lc.
  - exact Hb.
Qed.

Lemma reducible_if : forall T rho eta c a b,
  reducible Ty_Bool rho eta c ->
  reducible T rho eta a -> reducible T rho eta b ->
  locally_closed_tm a -> locally_closed_tm b ->
  reducible T rho eta (tm_if c a b).
Proof.
  intros T rho eta c a b [v [Hm Hv]] Ha Hb Hla Hlb.
  destruct Hv as [_ [E|E]]; subst v.
  - destruct Ha as [z [Haz Hz]].
    exists z; split; auto.
    eapply multi_trans; [apply multi_if; eauto|].
    eapply multi_trans; [eapply multi_one; apply ST_IfTrue; eauto|].
    exact Haz.
  - destruct Hb as [z [Hbz Hz]].
    exists z; split; auto.
    eapply multi_trans; [apply multi_if; eauto|].
    eapply multi_trans; [eapply multi_one; apply ST_IfFalse; eauto|].
    exact Hbz.
Qed.

Lemma reducible_succ : forall rho eta t,
  reducible Ty_Nat rho eta t ->
  reducible Ty_Nat rho eta (tm_succ t).
Proof.
  intros rho eta t [n [Hm Hn]].
  exists (tm_succ n); split.
  - apply multi_succ; assumption.
  - apply realizes_nat; constructor; exact (proj2 Hn).
Qed.

Lemma reducible_rec_value : forall T rho eta n b s,
  numeric_value n -> realizes T rho eta b ->
  realizes (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho eta s ->
  reducible T rho eta (tm_natrec n b s).
Proof.
  intros T rho eta n b s Hn; induction Hn; intros Hb Hs.
  - exists b; split; auto.
    eapply multi_one; apply ST_RecZero;
      eauto using realizes_value.
  - assert (Hr : reducible T rho eta (tm_natrec n b s)).
    { apply IHHn; assumption. }
    assert (Hsn : reducible (Ty_Arrow T T) rho eta (tm_app s n)).
    { eapply reducible_app.
      - exists s; split; [constructor|exact Hs].
      - exists n; split; [constructor|apply realizes_nat; assumption].
      - apply value_lc; constructor; assumption. }
    assert (Happ : reducible T rho eta
                     (tm_app (tm_app s n) (tm_natrec n b s))).
    { eapply reducible_app; eauto.
      unfold locally_closed_tm.
      apply lc_tm_rec.
      - apply value_lc; constructor; assumption.
      - apply value_lc; apply realizes_value with (T:=T) (rho:=rho) (eta:=eta); assumption.
      - apply value_lc; apply realizes_value with (T:=Ty_Arrow Ty_Nat (Ty_Arrow T T))
          (rho:=rho) (eta:=eta); assumption. }
    eapply reducible_step_back; [apply ST_RecSucc|exact Happ];
      eauto using realizes_value.
Qed.

Lemma reducible_rec : forall T rho eta n b s,
  reducible Ty_Nat rho eta n ->
  reducible T rho eta b ->
  reducible (Ty_Arrow Ty_Nat (Ty_Arrow T T)) rho eta s ->
  locally_closed_tm b -> locally_closed_tm s ->
  reducible T rho eta (tm_natrec n b s).
Proof.
  intros T rho eta n b s [vn [Hn Hvn]] [vb [Hb Hvb]]
    [vs [Hs Hvs]] Hlb Hls.
  destruct Hvn as [_ Hnum].
  destruct (reducible_rec_value T rho eta vn vb vs Hnum Hvb Hvs)
    as [z [Hrec Hz]].
  exists z; split; auto.
  eapply multi_trans; [apply multi_rec_arg; eauto|].
  eapply multi_trans; [apply multi_rec_base; eauto using value_lc, realizes_value|].
  eapply multi_trans; [apply multi_rec_step; eauto using realizes_value|].
  exact Hrec.
Qed.

Lemma reducible_equiv : forall A B rho eta t,
  (forall v, realizes A rho eta v <-> realizes B rho eta v) ->
  reducible A rho eta t -> reducible B rho eta t.
Proof.
  intros A B rho eta t He [v [Hm Hv]].
  exists v; split; auto; apply He; assumption.
Qed.

Lemma realizes_open_top : forall T U rho eta v,
  lc_ty_at 1 T -> locally_closed_ty U ->
  (realizes (open_ty T U) rho eta v <->
   realizes T (realizes U rho eta :: rho) eta v).
Proof.
  intros T U rho eta v HT HU.
  unfold open_ty.
  eapply iff_trans.
  - apply (realizes_open_ty T 0 U eta [] rho v HT HU eq_refl).
  - simpl.
    eapply realizes_ext.
    + intros [|i]; simpl.
      * unfold cand_equiv; intros w.
        eapply realizes_lc_env; eauto.
        intros j Hj; lia.
      * unfold cand_equiv; tauto.
    + intros X HX; unfold cand_equiv; tauto.
Qed.

Definition override_ty (theta : atom -> ty) (X : atom) (U : ty) :
  atom -> ty :=
  fun Y => if Nat.eqb X Y then U else theta Y.

Definition override_cand (eta : atom -> candidate) (X : atom)
    (Q : candidate) : atom -> candidate :=
  fun Y => if Nat.eqb X Y then Q else eta Y.

Definition override_tm (sigma : atom -> tm) (x : atom) (v : tm) :
  atom -> tm :=
  fun y => if Nat.eqb x y then v else sigma y.

Lemma realizes_open_fvar : forall T X rho eta Q v,
  lc_ty_at 1 T -> ~ In X (fv_ty T) ->
  (forall w, Q w -> value w) ->
  (realizes (open_ty T (Ty_FVar X)) rho
      (override_cand eta X Q) v <->
   realizes T (Q::rho) eta v).
Proof.
  intros T X rho eta Q v HT HX HQ.
  unfold open_ty.
  eapply iff_trans.
  - apply (realizes_open_ty T 0 (Ty_FVar X)
      (override_cand eta X Q) [] rho v HT).
    + unfold locally_closed_ty; constructor.
    + reflexivity.
  - simpl.
    eapply realizes_ext.
    + intros [|i]; simpl.
      * unfold cand_equiv, override_cand; intro w.
        rewrite Nat.eqb_refl; simpl; split.
        -- intros [_ Hq]; exact Hq.
        -- intros Hq; split; auto.
      * unfold cand_equiv; tauto.
    + intros Y HY; unfold cand_equiv, override_cand.
      destruct (Nat.eqb X Y) eqn:E.
      * apply Nat.eqb_eq in E; subst; contradiction.
      * tauto.
Qed.

Lemma fv_tm_map_ty : forall t theta,
  fv_tm (map_tm_ty theta t) = fv_tm t.
Proof.
  induction t; intros theta; simpl;
    repeat match goal with
    | H : forall theta, fv_tm (map_tm_ty theta ?u) = fv_tm ?u |- _ =>
        rewrite (H theta)
    end; reflexivity.
Qed.

Lemma override_tm_good : forall sigma x v,
  (forall y, locally_closed_tm (sigma y)) ->
  locally_closed_tm v ->
  forall y, locally_closed_tm (override_tm sigma x v y).
Proof.
  intros sigma x v Hs Hv y; unfold override_tm.
  destruct (Nat.eqb x y); auto.
Qed.

Lemma override_ty_good : forall theta X U,
  (forall Y, locally_closed_ty (theta Y)) ->
  locally_closed_ty U ->
  forall Y, locally_closed_ty (override_ty theta X U Y).
Proof.
  intros theta X U Ht HU Y; unfold override_ty.
  destruct (Nat.eqb X Y); auto.
Qed.

Lemma close_tm_open : forall t theta sigma x v,
  ~ In x (fv_tm t) ->
  (forall y, locally_closed_tm (sigma y)) ->
  locally_closed_tm v ->
  close_tm theta (override_tm sigma x v)
    (open_tm t (tm_fvar x)) =
  open_tm (close_tm theta sigma t) v.
Proof.
  intros t theta sigma x v Hfresh Hsigma Hv.
  unfold close_tm, open_tm.
  rewrite map_tm_ty_open_tm.
  rewrite map_tm_open by (apply override_tm_good; assumption).
  unfold override_tm at 1; rewrite Nat.eqb_refl.
  f_equal.
  apply map_tm_ext; intros y Hy.
  rewrite fv_tm_map_ty in Hy.
  unfold override_tm; destruct (Nat.eqb x y) eqn:E; auto.
  apply Nat.eqb_eq in E; subst; contradiction.
Qed.

Lemma close_tm_ty_open : forall t theta sigma X U,
  ~ In X (fv_tm_ty t) ->
  (forall Y, locally_closed_ty (theta Y)) ->
  locally_closed_ty U ->
  (forall y, locally_closed_tm (sigma y)) ->
  close_tm (override_ty theta X U) sigma
    (open_tm_ty t (Ty_FVar X)) =
  open_tm_ty (close_tm theta sigma t) U.
Proof.
  intros t theta sigma X U Hfresh Htheta HU Hsigma.
  unfold close_tm, open_tm_ty.
  rewrite map_tm_ty_open_ty by (apply override_ty_good; assumption).
  rewrite map_tm_open_ty by assumption.
  unfold override_ty at 1; rewrite Nat.eqb_refl.
  f_equal; f_equal.
  apply map_tm_ty_ext; intros Y HY.
  unfold override_ty; destruct (Nat.eqb X Y) eqn:E; auto.
  apply Nat.eqb_eq in E; subst; contradiction.
Qed.

Lemma notin_app_l : forall (x : atom) a b,
  ~ In x (a ++ b) -> ~ In x a.
Proof. intros x a b H Hin; apply H, in_or_app; auto. Qed.

Lemma notin_app_r : forall (x : atom) a b,
  ~ In x (a ++ b) -> ~ In x b.
Proof. intros x a b H Hin; apply H, in_or_app; auto. Qed.

Lemma lookup_notin_dom : forall Gamma x,
  ~ In x (dom_gamma Gamma) -> lookup_context x Gamma = None.
Proof.
  induction Gamma as [|[y T] Gamma IH]; intros x H; simpl in *; auto.
  assert (x <> y) by (intro E; subst; apply H; simpl; auto).
  apply Nat.eqb_neq in H0; rewrite H0.
  apply IH; intros Hin; apply H; simpl; auto.
Qed.

Lemma lookup_update_same : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros; simpl; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma lookup_update_other : forall Gamma x y T,
  x <> y -> lookup_context y (update Gamma x T) = lookup_context y Gamma.
Proof.
  intros; simpl; apply Nat.eqb_neq in H; rewrite Nat.eqb_sym, H;
    reflexivity.
Qed.

Lemma lookup_in_dom : forall Gamma x T,
  lookup_context x Gamma = Some T -> In x (dom_gamma Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T H; simpl in *;
    [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - apply Nat.eqb_eq in E; subst; simpl; auto.
  - right; apply IH with T; assumption.
Qed.

Lemma lookup_ty_fv : forall Gamma x T X,
  lookup_context x Gamma = Some T ->
  In X (fv_ty T) -> In X (fv_gamma_ty Gamma).
Proof.
  induction Gamma as [|[y U] Gamma IH]; intros x T X Hlookup HX;
    simpl in *; [discriminate|].
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlookup; subst; apply in_or_app; auto.
  - apply in_or_app; right; eapply IH; eauto.
Qed.

Definition env_good (Gamma : context) (rho : list candidate)
    (eta : atom -> candidate) (sigma : atom -> tm) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    realizes T rho eta (sigma x).

Lemma env_good_tm_extend : forall Gamma rho eta sigma x T v,
  env_good Gamma rho eta sigma ->
  realizes T rho eta v ->
  env_good (update Gamma x T) rho eta (override_tm sigma x v).
Proof.
  intros Gamma rho eta sigma x T v Henv Hv y U Hlook.
  unfold override_tm; simpl in Hlook.
  replace (y =? x) with (x =? y) in Hlook by apply Nat.eqb_sym.
  destruct (Nat.eqb x y) eqn:E.
  - inversion Hlook; subst.
    exact Hv.
  - apply Henv; exact Hlook.
Qed.

Lemma env_good_ty_extend : forall Gamma rho eta sigma X Q,
  ~ In X (fv_gamma_ty Gamma) ->
  env_good Gamma rho eta sigma ->
  env_good Gamma rho (override_cand eta X Q) sigma.
Proof.
  intros Gamma rho eta sigma X Q Hfresh Henv x T Hlook.
  assert (Hr : rho_equiv rho rho).
  { intros i; unfold cand_equiv; tauto. }
  assert (He : forall Y, In Y (fv_ty T) ->
            cand_equiv (eta Y) (override_cand eta X Q Y)).
  { intros Y HY; unfold cand_equiv, override_cand.
    destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      exfalso; apply Hfresh.
      eapply lookup_ty_fv; eauto.
    + tauto. }
  apply (proj1 (realizes_ext T rho rho eta
    (override_cand eta X Q) (sigma x) Hr He)).
  apply Henv; assumption.
Qed.

Lemma map_ty_identity : forall T,
  map_ty (fun X => Ty_FVar X) T = T.
Proof. induction T; simpl; f_equal; auto. Qed.

Lemma map_tm_ty_identity : forall t,
  map_tm_ty (fun X => Ty_FVar X) t = t.
Proof.
  induction t; simpl; try reflexivity;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3, ?map_ty_identity;
         reflexivity).
Qed.

Lemma map_tm_identity : forall t,
  map_tm (fun x => tm_fvar x) t = t.
Proof.
  induction t; simpl; try reflexivity;
    try (rewrite ?IHt, ?IHt1, ?IHt2, ?IHt3; reflexivity).
Qed.

Lemma close_tm_identity : forall t,
  close_tm (fun X => Ty_FVar X) (fun x => tm_fvar x) t = t.
Proof.
  intro t; unfold close_tm.
  rewrite map_tm_ty_identity, map_tm_identity; reflexivity.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho eta theta sigma,
    (forall X, locally_closed_ty (theta X)) ->
    (forall x, locally_closed_tm (sigma x)) ->
    env_good Gamma rho eta sigma ->
    reducible T rho eta (close_tm theta sigma t).
Proof.
  intros Delta Gamma t T Htyp; induction Htyp;
    intros rho eta theta sigma Htheta Hsigma Henv;
    unfold close_tm in *; simpl.
  - exists (sigma x); split; [constructor|apply Henv; assumption].
  - destruct (fresh_list (L ++ fv_tm t2)) as [x Hfresh].
    assert (HxL : ~ In x L).
    { eapply notin_app_l; eauto. }
    assert (Hxt : ~ In x (fv_tm t2)).
    { eapply notin_app_r; eauto. }
    exists (tm_abs (map_ty theta T1)
                   (map_tm sigma (map_tm_ty theta t2))).
    split; [constructor|].
    simpl; split.
    + apply v_abs.
      change (locally_closed_tm
        (close_tm theta sigma (tm_abs T1 t2))).
      eapply close_tm_lc; eauto.
      eapply typing_lc.
      eapply T_Abs with (L:=L); eauto.
    + intros v Hv.
      assert (Hvlc : locally_closed_tm v).
      { apply value_lc; eapply realizes_value; eauto. }
      pose proof (H1 x HxL rho eta theta
        (override_tm sigma x v) Htheta
        (override_tm_good sigma x v Hsigma Hvlc)
        (env_good_tm_extend Gamma rho eta sigma x T1 v Henv Hv))
        as Hbody.
      change (reducible T2 rho eta
        (close_tm theta (override_tm sigma x v)
           (open_tm t2 (tm_fvar x)))) in Hbody.
      rewrite close_tm_open in Hbody; eauto.
  - eapply reducible_app; eauto.
    eapply close_tm_lc; eauto.
    eapply typing_lc; eauto.
  - destruct (fresh_list
      (L ++ fv_tm_ty t ++ fv_ty T ++ fv_gamma_ty Gamma)) as [X Hfresh].
    assert (HXL : ~ In X L).
    { eapply notin_app_l; eauto. }
    assert (HXt : ~ In X (fv_tm_ty t)).
    { apply notin_app_l with (b:=fv_ty T ++ fv_gamma_ty Gamma).
      eapply notin_app_r; eauto. }
    assert (HXT : ~ In X (fv_ty T)).
    { apply notin_app_l with (b:=fv_gamma_ty Gamma).
      apply notin_app_r with (a:=fv_tm_ty t).
      eapply notin_app_r; eauto. }
    assert (HXG : ~ In X (fv_gamma_ty Gamma)).
    { apply notin_app_r with (a:=fv_ty T).
      apply notin_app_r with (a:=fv_tm_ty t).
      eapply notin_app_r; eauto. }
    assert (HTlc : lc_ty_at 1 T).
    { eapply lc_ty_open_inv.
      eapply typing_type_lc; apply H; exact HXL. }
    exists (tm_tabs (map_tm sigma (map_tm_ty theta t))).
    split; [constructor|].
    simpl; split.
    + apply v_tabs.
      change (locally_closed_tm (close_tm theta sigma (tm_tabs t))).
      eapply close_tm_lc; eauto.
      eapply typing_lc.
      eapply T_TAbs with (L:=L); eauto.
    + intros U Q HU HQ.
      pose proof (H0 X HXL rho (override_cand eta X Q)
        (override_ty theta X U) sigma
        (override_ty_good theta X U Htheta HU)
        Hsigma
        (env_good_ty_extend Gamma rho eta sigma X Q HXG Henv))
        as Hbody.
      destruct Hbody as [z [Hm Hz]].
      exists z; split.
      * change (multi
          (close_tm (override_ty theta X U) sigma
            (open_tm_ty t (Ty_FVar X))) z) in Hm.
        rewrite close_tm_ty_open in Hm; eauto.
      * apply (proj1 (realizes_open_fvar T X rho eta Q z
           HTlc HXT HQ)); exact Hz.
  - assert (HUl : locally_closed_ty (map_ty theta U)).
    { eapply map_ty_lc.
      - eapply wf_lc; eassumption.
      - exact Htheta. }
    destruct (reducible_tapp T rho eta
       (map_tm sigma (map_tm_ty theta t)) (map_ty theta U)
       (realizes U rho eta) (IHHtyp rho eta theta sigma Htheta Hsigma Henv)
       HUl (fun v Hv => realizes_value U rho eta v Hv))
      as [z [Hm Hz]].
    exists z; split; auto.
    assert (HTlc : lc_ty_at 1 T).
    { pose proof (typing_type_lc _ _ _ _ Htyp) as Hlc.
      inversion Hlc; subst; assumption. }
    apply (proj2 (realizes_open_top T U rho eta z HTlc
       (wf_lc Delta U H))); exact Hz.
  - exists tm_true; split; [constructor|simpl; auto using value].
  - exists tm_false; split; [constructor|simpl; auto using value].
  - eapply reducible_if; eauto;
      eapply close_tm_lc; eauto using typing_lc.
  - exists tm_zero; split; [constructor|apply realizes_nat; constructor].
  - apply reducible_succ; eauto.
  - eapply reducible_rec; eauto;
      eapply close_tm_lc; eauto using typing_lc.
Qed.

Lemma step_deterministic : forall t u v,
  step t u -> step t v -> u = v.
Proof.
  intros t u v H; revert v; induction H; intros w H';
    inversion H'; subst; try reflexivity;
    try solve [
      match goal with
      | Hv : value ?a, Hs : step ?a _ |- _ =>
          exfalso; exact (value_no_step a _ Hv Hs)
      | Hn : numeric_value ?a, Hs : step ?a _ |- _ =>
          exfalso; exact (numeric_value_no_step a _ Hn Hs)
      | Hn : numeric_value ?a, Hs : step (tm_succ ?a) _ |- _ =>
          exfalso; exact (numeric_value_no_step (tm_succ a) _
            (nv_succ a Hn) Hs)
      end ];
    try solve [
      match goal with
      | Hs : step (tm_abs _ _) _ |- _ => inversion Hs
      | Hs : step (tm_tabs _) _ |- _ => inversion Hs
      | Hs : step tm_zero _ |- _ => inversion Hs
      | Hs : step tm_true _ |- _ => inversion Hs
      | Hs : step tm_false _ |- _ => inversion Hs
      end ];
    try (f_equal; eauto).
Qed.

Lemma multi_value_sn : forall t v,
  multi t v -> value v -> strongly_normalizing t.
Proof.
  intros t v Hm; induction Hm; intros Hv.
  - apply SN_intro; intros u Hu.
    exfalso; eapply value_no_step; eauto.
  - apply SN_intro; intros u Hu.
    assert (u = y) by (eapply step_deterministic; eauto).
    subst u; apply IHHm; assumption.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Htyp.
  pose proof (fundamental [] empty t T Htyp []
    (fun _ _ => False) (fun X => Ty_FVar X) (fun x => tm_fvar x))
    as Hfund.
  assert (Htheta : forall X, locally_closed_ty (Ty_FVar X)).
  { intros X; unfold locally_closed_ty; constructor. }
  assert (Hsigma : forall x, locally_closed_tm (tm_fvar x)).
  { intros x; unfold locally_closed_tm; constructor. }
  assert (Henv : env_good empty [] (fun _ _ => False)
                  (fun x => tm_fvar x)).
  { intros x U Hlookup; discriminate. }
  specialize (Hfund Htheta Hsigma Henv).
  rewrite close_tm_identity in Hfund.
  destruct Hfund as [v [Hm Hv]].
  eapply multi_value_sn; eauto using realizes_value.
Qed.

End SystemFNormalizationIfRecursionHardTask.
