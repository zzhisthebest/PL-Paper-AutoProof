(** System F parametricity benchmark, Hard variant.
    Features: if-recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityIfRecursionHardTask.

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

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H; induction H; unfold locally_closed_tm in *.
  - constructor.
  - constructor; assumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H; inversion H; subst.
  - exact H0.
  - exact H0.
  - unfold locally_closed_tm; constructor.
  - unfold locally_closed_tm; constructor.
  - eapply numeric_value_lc; eassumption.
Qed.

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

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof.
  intros t u v H; induction H; intros Huv.
  - exact Huv.
  - econstructor; eauto.
Qed.

Lemma multi_one : forall t u, t --> u -> t -->* u.
Proof.
  intros; econstructor; [eassumption|constructor].
Qed.

Lemma numeric_value_no_step : forall n u, numeric_value n -> ~ (n --> u).
Proof.
  intros n u Hn; revert u; induction Hn; intros u Hs.
  - inversion Hs.
  - inversion Hs; subst. eapply IHHn; eassumption.
Qed.

Lemma value_no_step : forall v u, value v -> ~ (v --> u).
Proof.
  intros v u Hv Hs. inversion Hv; subst; try solve [inversion Hs];
    eapply numeric_value_no_step; eauto.
Qed.

Definition term_relation := tm -> tm -> Prop.
Record rel_env_entry := {
  rel_env_name : atom;
  rel_env_left_ty : ty;
  rel_env_right_ty : ty;
  rel_env_rel : term_relation
}.
Definition rel_env := list rel_env_entry.

Fixpoint lookup_rel_env (X : atom) (rho : rel_env) : option rel_env_entry :=
  match rho with
  | [] => None
  | e :: rho' =>
      if Nat.eqb X (rel_env_name e) then Some e else lookup_rel_env X rho'
  end.

Fixpoint value_rel (rho : rel_env) (bs : list term_relation)
    (T1 T2 : ty) {struct T1} : term_relation :=
  match T1, T2 with
  | Ty_FVar X, Ty_FVar Y =>
      fun v1 v2 => exists e, X = Y /\ lookup_rel_env X rho = Some e /\ rel_env_rel e v1 v2
  | Ty_BVar i, Ty_BVar j =>
      fun v1 v2 => exists R, i = j /\ nth_error bs i = Some R /\ R v1 v2
  | Ty_Arrow A B, Ty_Arrow C D =>
      fun v1 v2 => value v1 /\ value v2 /\
        (forall a1 a2, value a1 -> value a2 -> value_rel rho bs A C a1 a2 ->
          exists w1 w2,
            multi (tm_app v1 a1) w1 /\ multi (tm_app v2 a2) w2 /\
            value w1 /\ value w2 /\ value_rel rho bs B D w1 w2)
  | Ty_All A, Ty_All B =>
      fun v1 v2 => exists t1 t2, v1 = tm_tabs t1 /\ v2 = tm_tabs t2 /\
        value v1 /\ value v2 /\
        (forall U V R, locally_closed_ty U -> locally_closed_ty V ->
          forall w1 w2,
            multi (open_tm_ty t1 U) w1 -> multi (open_tm_ty t2 V) w2 ->
            value w1 -> value w2 -> value_rel rho (R :: bs) A B w1 w2)
  | Ty_Bool, Ty_Bool =>
      fun v1 v2 => (v1 = tm_true /\ v2 = tm_true) \/
                   (v1 = tm_false /\ v2 = tm_false)
  | Ty_Nat, Ty_Nat => fun v1 v2 => exists n, v1 = numeral n /\ v2 = numeral n
  | _, _ => fun _ _ => False
  end.

Lemma value_rel_stack_eq : forall T1,
  (forall T2 rho K bs1 bs2 v1 v2,
    lc_ty_at K T1 -> lc_ty_at K T2 ->
    (forall i, i < K -> nth_error bs1 i = nth_error bs2 i) ->
    (value_rel rho bs1 T1 T2 v1 v2 <-> value_rel rho bs2 T1 T2 v1 v2))%type.
Proof.
  induction T1; intros T2 rho K bs1 bs2 v1 v2 Hlc1 Hlc2 Hst;
    destruct T2; simpl in *; try tauto.
  - assert (Hbound : n0 < K) by (inversion Hlc2; lia).
    split; intros [R [Heq [Hnth Hrel]]]; subst.
    + exists R; repeat split; try assumption. rewrite <- (Hst n0 Hbound); exact Hnth.
    + exists R; repeat split; try assumption. rewrite (Hst n0 Hbound); exact Hnth.
  - inversion Hlc1; subst. inversion Hlc2; subst.
    split; intros [Hv1 [Hv2 Hfun]]; repeat split; try assumption.
    + intros a1 a2 Hva1 Hva2 Ha2.
      pose proof (proj2 (IHT1_1 T2_1 rho K bs1 bs2 a1 a2 H2 H4 Hst) Ha2) as Ha1.
      destruct (Hfun a1 a2 Hva1 Hva2 Ha1) as [w1 [w2 [Hm1 [Hm2 [Hvw1 [Hvw2 Hrel]]]]]].
      exists w1, w2; repeat split; try assumption.
      apply (proj1 (IHT1_2 T2_2 rho K bs1 bs2 w1 w2 H3 H5 Hst)); exact Hrel.
    + intros a1 a2 Hva1 Hva2 Ha1.
      pose proof (proj1 (IHT1_1 T2_1 rho K bs1 bs2 a1 a2 H2 H4 Hst) Ha1) as Ha2.
      destruct (Hfun a1 a2 Hva1 Hva2 Ha2) as [w1 [w2 [Hm1 [Hm2 [Hvw1 [Hvw2 Hrel]]]]]].
      exists w1, w2; repeat split; try assumption.
      apply (proj2 (IHT1_2 T2_2 rho K bs1 bs2 w1 w2 H3 H5 Hst)); exact Hrel.
  - inversion Hlc1; subst. inversion Hlc2; subst.
    split.
    + intros [b1 [b2 [E1 [E2 [Hv1 [Hv2 Hfun]]]]]].
      exists b1, b2; repeat split; try assumption.
      intros U V R HwfU HwfV w1 w2 Hm1 Hm2 Hvw1 Hvw2.
      assert (Hst' : forall i, i < S K -> nth_error (R :: bs1) i = nth_error (R :: bs2) i).
      { intros [|i] Hlt; simpl; [reflexivity|apply Hst; lia]. }
      apply (proj1 (IHT1 T2 rho (S K) (R :: bs1) (R :: bs2) w1 w2 H1 H2 Hst')).
      exact (Hfun U V R HwfU HwfV w1 w2 Hm1 Hm2 Hvw1 Hvw2).
    + intros [b1 [b2 [E1 [E2 [Hv1 [Hv2 Hfun]]]]]].
      exists b1, b2; repeat split; try assumption.
      intros U V R HwfU HwfV w1 w2 Hm1 Hm2 Hvw1 Hvw2.
      assert (Hst' : forall i, i < S K -> nth_error (R :: bs1) i = nth_error (R :: bs2) i).
      { intros [|i] Hlt; simpl; [reflexivity|apply Hst; lia]. }
      apply (proj2 (IHT1 T2 rho (S K) (R :: bs1) (R :: bs2) w1 w2 H1 H2 Hst')).
      exact (Hfun U V R HwfU HwfV w1 w2 Hm1 Hm2 Hvw1 Hvw2).
Qed.

Lemma value_rel_stack_equiv : forall T,
  forall rho K bs1 bs2 v1 v2,
    lc_ty_at K T ->
    (forall i, i < K -> exists R1 R2,
      nth_error bs1 i = Some R1 /\ nth_error bs2 i = Some R2 /\
      (forall a b, R1 a b <-> R2 a b)) ->
    (value_rel rho bs1 T T v1 v2 <-> value_rel rho bs2 T T v1 v2).
Proof.
  induction T; intros rho K bs1 bs2 v1 v2 Hlc Hst; simpl in *.
  - inversion Hlc; subst.
    assert (Hbound : n < K) by assumption.
    split.
    + intros [R [_ [Hnth Hrel]]].
      destruct (Hst n Hbound) as [R1 [R2 [Hnth1 [Hnth2 Hiff]]]].
      assert (Hsome : Some R = Some R1).
      { transitivity (nth_error bs1 n); [symmetry; exact Hnth|exact Hnth1]. }
      injection Hsome as HeqR; subst R1.
      exists R2; repeat split; try assumption. apply (proj1 (Hiff v1 v2)); exact Hrel.
    + intros [R [_ [Hnth Hrel]]].
      destruct (Hst n Hbound) as [R1 [R2 [Hnth1 [Hnth2 Hiff]]]].
      assert (Hsome : Some R = Some R2).
      { transitivity (nth_error bs2 n); [symmetry; exact Hnth|exact Hnth2]. }
      injection Hsome as HeqR; subst R2.
      exists R1; repeat split; try assumption. apply (proj2 (Hiff v1 v2)); exact Hrel.
  - tauto.
  - inversion Hlc; subst.
    split.
    + intros [Hv1 [Hv2 Hfun]]. repeat split; try assumption.
      intros a1 a2 Hva1 Hva2 Ha.
      pose proof (proj2 (IHT1 rho K bs1 bs2 a1 a2 H2 Hst) Ha) as Ha1.
      destruct (Hfun a1 a2 Hva1 Hva2 Ha1) as [w1 [w2 [Hm1 [Hm2 [Hw1 [Hw2 Hrel]]]]]].
      exists w1,w2; repeat split; try assumption.
      apply (proj1 (IHT2 rho K bs1 bs2 w1 w2 H3 Hst)); exact Hrel.
    + intros [Hv1 [Hv2 Hfun]]. repeat split; try assumption.
      intros a1 a2 Hva1 Hva2 Ha.
      pose proof (proj1 (IHT1 rho K bs1 bs2 a1 a2 H2 Hst) Ha) as Ha1.
      destruct (Hfun a1 a2 Hva1 Hva2 Ha1) as [w1 [w2 [Hm1 [Hm2 [Hw1 [Hw2 Hrel]]]]]].
      exists w1,w2; repeat split; try assumption.
      apply (proj2 (IHT2 rho K bs1 bs2 w1 w2 H3 Hst)); exact Hrel.
  - inversion Hlc; subst.
    split.
    + intros [b1 [b2 [E1 [E2 [Hv1 [Hv2 Hfun]]]]]].
      exists b1,b2; repeat split; try assumption.
      intros U V R HwfU HwfV w1 w2 Hm1 Hm2 Hw1 Hw2.
      assert (Hst' : forall i, i < S K -> exists R1 R2,
        nth_error (R :: bs1) i = Some R1 /\ nth_error (R :: bs2) i = Some R2 /\
        (forall a b, R1 a b <-> R2 a b)).
      { intros [|i] Hlt.
        - exists R,R. simpl. split; [reflexivity|]. split; [reflexivity|]. intros; tauto.
        - pose proof (Hst i ltac:(lia)) as Hpair. destruct Hpair as [R1 [R2 [E1' [E2' Hiff]]]].
          exists R1,R2. simpl. split; [exact E1'|]. split; [exact E2'|exact Hiff]. }
      apply (proj1 (IHT rho (S K) (R::bs1) (R::bs2) w1 w2 H1 Hst')).
      exact (Hfun U V R HwfU HwfV w1 w2 Hm1 Hm2 Hw1 Hw2).
    + intros [b1 [b2 [E1 [E2 [Hv1 [Hv2 Hfun]]]]]].
      exists b1,b2; repeat split; try assumption.
      intros U V R HwfU HwfV w1 w2 Hm1 Hm2 Hw1 Hw2.
      assert (Hst' : forall i, i < S K -> exists R1 R2,
        nth_error (R :: bs1) i = Some R1 /\ nth_error (R :: bs2) i = Some R2 /\
        (forall a b, R1 a b <-> R2 a b)).
      { intros [|i] Hlt.
        - exists R,R. simpl. split; [reflexivity|]. split; [reflexivity|]. intros; tauto.
        - pose proof (Hst i ltac:(lia)) as Hpair. destruct Hpair as [R1 [R2 [E1' [E2' Hiff]]]].
          exists R1,R2. simpl. split; [exact E1'|]. split; [exact E2'|exact Hiff]. }
      apply (proj2 (IHT rho (S K) (R::bs1) (R::bs2) w1 w2 H1 Hst')).
      exact (Hfun U V R HwfU HwfV w1 w2 Hm1 Hm2 Hw1 Hw2).
  - tauto.
  - tauto.
Qed.

Lemma value_rel_open_ty_rec : forall T,
  forall rho inner outer U V v1 v2,
    lc_ty_at (S (length inner)) T ->
    locally_closed_ty U -> locally_closed_ty V ->
    (value_rel rho (inner ++ (value_rel rho (inner ++ outer) U V) :: outer) T T v1 v2 <->
     value_rel rho (inner ++ outer)
       (open_ty_rec (length inner) U T) (open_ty_rec (length inner) V T) v1 v2).
Proof.
  induction T; intros rho inner outer U V v1 v2 Hlc HlcU HlcV; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb (length inner) n) eqn:E.
    + apply Nat.eqb_eq in E.
      assert (Hnthbound : nth_error
        (inner ++ value_rel rho (inner ++ outer) U V :: outer) n =
        Some (value_rel rho (inner ++ outer) U V)).
      { rewrite nth_error_app2 by lia. rewrite E. replace (n - n) with 0 by lia. reflexivity. }
      assert (Hshort : n = length inner) by lia.
      split.
      * intros [R [_ [Hnth Hrel]]]. rewrite Hnthbound in Hnth. injection Hnth as Hident. subst R. exact Hrel.
      * intros Hrel. exists (value_rel rho (inner ++ outer) U V); repeat split; try reflexivity; try assumption.
    + apply Nat.eqb_neq in E.
      assert (Hshort : n < length inner) by lia.
      assert (Hnthsame : nth_error
        (inner ++ value_rel rho (inner ++ outer) U V :: outer) n = nth_error (inner ++ outer) n).
      { rewrite !nth_error_app1; try lia; reflexivity. }
      split.
      * intros [R [Heq [Hnth Hrel]]]. exists R; repeat split; try assumption.
        rewrite Hnthsame in Hnth. exact Hnth.
      * intros [R [Heq [Hnth Hrel]]]. exists R; repeat split; try assumption.
        rewrite Hnthsame. exact Hnth.
  - tauto.
  - inversion Hlc; subst.
    split.
    + intros [Hv1 [Hv2 Hfun]]. repeat split; try assumption.
      intros a1 a2 Hva1 Hva2 HaOpen.
      apply (proj2 (IHT1 rho inner outer U V a1 a2 H2 HlcU HlcV)) in HaOpen.
      destruct (Hfun a1 a2 Hva1 Hva2 HaOpen) as [w1 [w2 [Hm1 [Hm2 [Hvw1 [Hvw2 Hrel]]]]]].
      exists w1, w2; repeat split; try assumption.
      apply (proj1 (IHT2 rho inner outer U V w1 w2 H3 HlcU HlcV)); exact Hrel.
    + intros [Hv1 [Hv2 Hfun]]. repeat split; try assumption.
      intros a1 a2 Hva1 Hva2 HaBound.
      pose proof (proj1 (IHT1 rho inner outer U V a1 a2 H2 HlcU HlcV) HaBound) as HaOpen.
      destruct (Hfun a1 a2 Hva1 Hva2 HaOpen) as [w1 [w2 [Hm1 [Hm2 [Hvw1 [Hvw2 Hrel]]]]]].
      exists w1, w2; repeat split; try assumption.
      apply (proj2 (IHT2 rho inner outer U V w1 w2 H3 HlcU HlcV)); exact Hrel.
  - inversion Hlc; subst.
    split.
    + intros [b1 [b2 [E1 [E2 [Hv1 [Hv2 Hfun]]]]]].
      exists b1, b2; repeat split; try assumption.
      intros U' V' Q HwfU' HwfV' w1 w2 Hm1 Hm2 Hvw1 Hvw2.
      assert (Hclosed : forall bs1 bs2 a b,
          value_rel rho bs1 U V a b <-> value_rel rho bs2 U V a b).
      { intros bs1 bs2 a b. apply (value_rel_stack_eq U V rho 0 bs1 bs2 a b HlcU HlcV).
        intros i Hi; lia. }
      set (Rold := value_rel rho (inner ++ outer) U V).
      set (Rnew := value_rel rho ((Q :: inner) ++ outer) U V).
      assert (Hst : forall i, i < S (S (length inner)) -> exists R1 R2,
        nth_error ((Q :: inner) ++ Rold :: outer) i = Some R1 /\
        nth_error ((Q :: inner) ++ Rnew :: outer) i = Some R2 /\
        (forall a b, R1 a b <-> R2 a b)).
      { intros i Hi.
        destruct (Nat.lt_ge_cases i (length (Q :: inner))) as [Hbefore|Hafter].
        - destruct (nth_error (Q :: inner) i) as [R0|] eqn:Enth.
          + exists R0,R0. rewrite !nth_error_app1 by exact Hbefore.
            split; [exact Enth|]. split; [exact Enth|]. intros; tauto.
          + apply nth_error_None in Enth. simpl in Enth. simpl in Hbefore. exfalso; lia.
        - assert (Ei : i = length (Q :: inner)) by (simpl in *; lia).
          subst i. exists Rold,Rnew.
          rewrite !nth_error_app2 by lia.
          replace (length (Q :: inner) - length (Q :: inner)) with 0 by lia.
          simpl.
          split; [reflexivity|]. split; [reflexivity|].
          intros a b. unfold Rold, Rnew.
          symmetry. apply (Hclosed ((Q :: inner) ++ outer) (inner ++ outer) a b). }
      pose proof (Hfun U' V' Q HwfU' HwfV' w1 w2 Hm1 Hm2 Hvw1 Hvw2) as Hbody.
      change (value_rel rho (Q :: inner ++ Rold :: outer) T T w1 w2) in Hbody.
      pose proof (proj1 (value_rel_stack_equiv T rho (S (S (length inner)))
        (Q :: inner ++ Rold :: outer) (Q :: inner ++ Rnew :: outer)
        w1 w2 H1 Hst) Hbody) as Hbody'.
      apply (proj1 (IHT rho (Q :: inner) outer U V w1 w2 H1 HlcU HlcV)).
      exact Hbody'.
    + intros [b1 [b2 [E1 [E2 [Hv1 [Hv2 Hfun]]]]]].
      exists b1, b2; repeat split; try assumption.
      intros U' V' Q HwfU' HwfV' w1 w2 Hm1 Hm2 Hvw1 Hvw2.
      set (Rold := value_rel rho (inner ++ outer) U V).
      set (Rnew := value_rel rho ((Q :: inner) ++ outer) U V).
      assert (Hclosed : forall bs1 bs2 a b,
          value_rel rho bs1 U V a b <-> value_rel rho bs2 U V a b).
      { intros bs1 bs2 a b. apply (value_rel_stack_eq U V rho 0 bs1 bs2 a b HlcU HlcV).
        intros i Hi; lia. }
      assert (Hst : forall i, i < S (S (length inner)) -> exists R1 R2,
        nth_error ((Q :: inner) ++ Rold :: outer) i = Some R1 /\
        nth_error ((Q :: inner) ++ Rnew :: outer) i = Some R2 /\
        (forall a b, R1 a b <-> R2 a b)).
      { intros i Hi.
        destruct (Nat.lt_ge_cases i (length (Q :: inner))) as [Hbefore|Hafter].
        - destruct (nth_error (Q :: inner) i) as [R0|] eqn:Enth.
          + exists R0,R0. rewrite !nth_error_app1 by exact Hbefore.
            split; [exact Enth|]. split; [exact Enth|]. intros; tauto.
          + apply nth_error_None in Enth. simpl in Enth. simpl in Hbefore. exfalso; lia.
        - assert (Ei : i = length (Q :: inner)) by (simpl in *; lia).
          subst i. exists Rold,Rnew.
          rewrite !nth_error_app2 by lia.
          replace (length (Q :: inner) - length (Q :: inner)) with 0 by lia.
          simpl. split; [reflexivity|]. split; [reflexivity|].
          intros a b. unfold Rold, Rnew.
          symmetry. apply (Hclosed ((Q :: inner) ++ outer) (inner ++ outer) a b). }
      pose proof (proj2 (IHT rho (Q :: inner) outer U V w1 w2 H1 HlcU HlcV)
        (Hfun U' V' Q HwfU' HwfV' w1 w2 Hm1 Hm2 Hvw1 Hvw2)) as Hnew.
      apply (proj2 (value_rel_stack_equiv T rho (S (S (length inner)))
        (Q :: inner ++ Rold :: outer) (Q :: inner ++ Rnew :: outer)
        w1 w2 H1 Hst)).
      exact Hnew.
  - tauto.
  - tauto.
Qed.

Fixpoint max_atom_list (xs : list atom) : nat :=
  match xs with [] => 0 | x :: xs' => Nat.max x (max_atom_list xs') end.
Definition fresh_atom (xs : list atom) : atom := S (max_atom_list xs).
Lemma in_le_max_atom_list : forall x xs, In x xs -> x <= max_atom_list xs.
Proof.
  intros x xs; induction xs as [|y ys IH]; simpl; intros Hin; [contradiction|].
  destruct Hin as [->|Hin].
  - apply Nat.le_max_l.
  - eapply Nat.le_trans; [apply IH; exact Hin|apply Nat.le_max_r].
Qed.
Lemma fresh_atom_notin : forall xs, ~ In (fresh_atom xs) xs.
Proof.
  intros xs Hin. unfold fresh_atom in Hin.
  pose proof (in_le_max_atom_list _ _ Hin). lia.
Qed.

Fixpoint ty_fvars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow A B => ty_fvars A ++ ty_fvars B
  | Ty_All A => ty_fvars A
  | Ty_Bool | Ty_Nat => []
  end.

Fixpoint tm_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs _ b | tm_tabs b | tm_succ b => tm_fvars b
  | tm_app a b => tm_fvars a ++ tm_fvars b
  | tm_tapp a _ => tm_fvars a
  | tm_true | tm_false | tm_zero => []
  | tm_if a b c | tm_natrec a b c => tm_fvars a ++ tm_fvars b ++ tm_fvars c
  end.

Fixpoint tm_ty_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ | tm_fvar _ | tm_true | tm_false | tm_zero => []
  | tm_abs T b => ty_fvars T ++ tm_ty_fvars b
  | tm_app a b => tm_ty_fvars a ++ tm_ty_fvars b
  | tm_tabs b | tm_succ b => tm_ty_fvars b
  | tm_tapp a T => tm_ty_fvars a ++ ty_fvars T
  | tm_if a b c | tm_natrec a b c => tm_ty_fvars a ++ tm_ty_fvars b ++ tm_ty_fvars c
  end.

Definition ty_context_atoms (Delta : ty_context) := Delta.
Fixpoint context_atoms (Gamma : context) : list atom :=
  match Gamma with [] => [] | (x, _) :: G => x :: context_atoms G end.
Fixpoint context_ty_fvars (Gamma : context) : list atom :=
  match Gamma with [] => [] | (_, T) :: G => ty_fvars T ++ context_ty_fvars G end.

Lemma lc_ty_open_inv : forall K T X,
  lc_ty_at K (open_ty_rec K (Ty_FVar X) T) -> lc_ty_at (S K) T.
Proof.
  intros K T; revert K; induction T; intros K X Hlc; simpl in *.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion Hlc; subst. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Hlc; subst. constructor; [eapply IHT1|eapply IHT2]; eassumption.
  - inversion Hlc; subst. constructor. eapply IHT. eassumption.
  - constructor.
  - constructor.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T Hwf; induction Hwf.
  - constructor.
  - econstructor; eassumption.
  - apply lc_ty_all.
    specialize (H0 (fresh_atom L) (fresh_atom_notin L)).
    eapply lc_ty_open_inv; exact H0.
  - constructor.
  - constructor.
Qed.

Lemma ty_fvars_open_contains : forall k T U Y,
  In Y (ty_fvars T) -> In Y (ty_fvars (open_ty_rec k U T)).
Proof.
  intros k T; revert k; induction T; intros k U Y Hin; simpl in *.
  - contradiction.
  - exact Hin.
  - apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff;
      [left; eapply IHT1|right; eapply IHT2]; eassumption.
  - eapply IHT; eassumption.
  - contradiction.
  - contradiction.
Qed.

Lemma wf_ty_fvars_in_context : forall Delta T,
  wf_ty Delta T -> forall X, In X (ty_fvars T) -> In X Delta.
Proof.
  intros Delta T Hwf; induction Hwf; intros Y Hin.
  - simpl in Hin. destruct Hin as [<-|[]]. assumption.
  - simpl in Hin. apply in_app_iff in Hin as [Hin|Hin].
    + eapply IHHwf1; eassumption.
    + eapply IHHwf2; eassumption.
  - set (Z := fresh_atom (Y :: L)).
    assert (HZL : ~ In Z L) by (unfold Z; intro Hbad; apply fresh_atom_notin with (xs:=Y::L); simpl; auto).
    assert (HZY : Z <> Y) by (unfold Z; intro Hbad; apply fresh_atom_notin with (xs:=Y::L); simpl; auto).
    assert (Hinopen : In Y (ty_fvars (open_ty T (Ty_FVar Z)))).
    { unfold open_ty. eapply ty_fvars_open_contains; exact Hin. }
    specialize (H0 Z HZL Y Hinopen).
    simpl in H0. destruct H0 as [Heq|HinD].
    + exfalso; apply HZY; exact Heq.
    + exact HinD.
  - contradiction.
  - contradiction.
Qed.

Lemma lc_tm_open_inv : forall K k t x,
  lc_tm_at K k (open_tm_rec k (tm_fvar x) t) -> lc_tm_at K (S k) t.
Proof.
  intros K k t; revert K k; induction t; intros K k x Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor; lia.
    + inversion Hlc; subst. constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Hlc; subst. apply lc_tm_abs.
    + assumption.
    + eapply IHt; eassumption.
  - inversion Hlc; subst. econstructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion Hlc; subst. apply lc_tm_tabs. eapply IHt; eassumption.
  - inversion Hlc; subst. econstructor; [eapply IHt; eassumption|assumption].
  - constructor.
  - constructor.
  - inversion Hlc; subst. econstructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
  - constructor.
  - inversion Hlc; subst. constructor. eapply IHt; eassumption.
  - inversion Hlc; subst. econstructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
Qed.

Lemma lc_tm_ty_open_inv : forall K k t X,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  intros K k t; revert K k; induction t; intros K k X Hlc; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - inversion Hlc; subst. constructor.
  - inversion Hlc; subst. apply lc_tm_abs.
    + eapply lc_ty_open_inv; eassumption.
    + eapply IHt; eassumption.
  - inversion Hlc; subst. econstructor; [eapply IHt1|eapply IHt2]; eassumption.
  - inversion Hlc; subst. apply lc_tm_tabs. eapply IHt; eassumption.
  - inversion Hlc; subst. econstructor; [eapply IHt|eapply lc_ty_open_inv]; eassumption.
  - constructor.
  - constructor.
  - inversion Hlc; subst. econstructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
  - constructor.
  - inversion Hlc; subst. constructor. eapply IHt; eassumption.
  - inversion Hlc; subst. econstructor; [eapply IHt1|eapply IHt2|eapply IHt3]; eassumption.
Qed.

Lemma has_type_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_tm_at 0 0 t.
Proof.
  intros Delta Gamma t T Hty; induction Hty.
  - constructor.
  - apply lc_tm_abs; [eapply wf_ty_lc; eassumption|].
    specialize (H1 (fresh_atom L) (fresh_atom_notin L)).
    eapply lc_tm_open_inv; exact H1.
  - econstructor; eassumption.
  - apply lc_tm_tabs. specialize (H0 (fresh_atom L) (fresh_atom_notin L)).
    eapply lc_tm_ty_open_inv; exact H0.
  - econstructor; [eassumption|eapply wf_ty_lc; eassumption].
  - constructor.
  - constructor.
  - econstructor; eassumption.
  - constructor.
  - econstructor; eassumption.
  - econstructor; eassumption.
Qed.

Fixpoint subst_ty_rel_left (rho : rel_env) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => match lookup_rel_env X rho with
                  | Some e => rel_env_left_ty e
                  | None => Ty_FVar X end
  | Ty_Arrow A B => Ty_Arrow (subst_ty_rel_left rho A) (subst_ty_rel_left rho B)
  | Ty_All A => Ty_All (subst_ty_rel_left rho A)
  | Ty_Bool => Ty_Bool
  | Ty_Nat => Ty_Nat
  end.

Fixpoint subst_ty_rel_right (rho : rel_env) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => match lookup_rel_env X rho with
                  | Some e => rel_env_right_ty e
                  | None => Ty_FVar X end
  | Ty_Arrow A B => Ty_Arrow (subst_ty_rel_right rho A) (subst_ty_rel_right rho B)
  | Ty_All A => Ty_All (subst_ty_rel_right rho A)
  | Ty_Bool => Ty_Bool
  | Ty_Nat => Ty_Nat
  end.

Lemma subst_ty_rel_left_identity_fvfree : forall rho T,
  (forall X, ~ In X (ty_fvars T)) -> subst_ty_rel_left rho T = T.
Proof.
  intros rho T; induction T; intros Hfree; simpl in *.
  - reflexivity.
  - destruct (lookup_rel_env a rho) as [e|] eqn:E.
    + exfalso. apply (Hfree a). simpl; auto.
    + reflexivity.
  - f_equal.
    + apply IHT1. intros Z Hin. apply (Hfree Z). apply in_or_app; left; exact Hin.
    + apply IHT2. intros Z Hin. apply (Hfree Z). apply in_or_app; right; exact Hin.
  - f_equal. apply IHT. exact Hfree.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_ty_rel_right_identity_fvfree : forall rho T,
  (forall X, ~ In X (ty_fvars T)) -> subst_ty_rel_right rho T = T.
Proof.
  intros rho T; induction T; intros Hfree; simpl in *.
  - reflexivity.
  - destruct (lookup_rel_env a rho) as [e|] eqn:E.
    + exfalso. apply (Hfree a). simpl; auto.
    + reflexivity.
  - f_equal.
    + apply IHT1. intros Z Hin. apply (Hfree Z). apply in_or_app; left; exact Hin.
    + apply IHT2. intros Z Hin. apply (Hfree Z). apply in_or_app; right; exact Hin.
  - f_equal. apply IHT. exact Hfree.
  - reflexivity.
  - reflexivity.
Qed.

Fixpoint subst_tm_ty_rel_left (rho : rel_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (subst_ty_rel_left rho T) (subst_tm_ty_rel_left rho b)
  | tm_app a b => tm_app (subst_tm_ty_rel_left rho a) (subst_tm_ty_rel_left rho b)
  | tm_tabs b => tm_tabs (subst_tm_ty_rel_left rho b)
  | tm_tapp a T => tm_tapp (subst_tm_ty_rel_left rho a) (subst_ty_rel_left rho T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if a b c => tm_if (subst_tm_ty_rel_left rho a) (subst_tm_ty_rel_left rho b) (subst_tm_ty_rel_left rho c)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (subst_tm_ty_rel_left rho a)
  | tm_natrec n b s => tm_natrec (subst_tm_ty_rel_left rho n) (subst_tm_ty_rel_left rho b) (subst_tm_ty_rel_left rho s)
  end.

Fixpoint subst_tm_ty_rel_right (rho : rel_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (subst_ty_rel_right rho T) (subst_tm_ty_rel_right rho b)
  | tm_app a b => tm_app (subst_tm_ty_rel_right rho a) (subst_tm_ty_rel_right rho b)
  | tm_tabs b => tm_tabs (subst_tm_ty_rel_right rho b)
  | tm_tapp a T => tm_tapp (subst_tm_ty_rel_right rho a) (subst_ty_rel_right rho T)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if a b c => tm_if (subst_tm_ty_rel_right rho a) (subst_tm_ty_rel_right rho b) (subst_tm_ty_rel_right rho c)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (subst_tm_ty_rel_right rho a)
  | tm_natrec n b s => tm_natrec (subst_tm_ty_rel_right rho n) (subst_tm_ty_rel_right rho b) (subst_tm_ty_rel_right rho s)
  end.

Definition term_subst_env := list (atom * (tm * tm)).
Fixpoint term_env_atoms (sigma : term_subst_env) : list atom :=
  match sigma with [] => [] | (x, _) :: s => x :: term_env_atoms s end.
Fixpoint rel_env_atoms (rho : rel_env) : list atom :=
  match rho with [] => [] | e :: r => rel_env_name e :: rel_env_atoms r end.

Lemma lookup_context_ty_fvars : forall Gamma x T X,
  lookup_context x Gamma = Some T -> In X (ty_fvars T) -> In X (context_ty_fvars Gamma).
Proof.
  intros Gamma; induction Gamma as [|[y A] G IH]; intros x T X Hlookup Hin; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x y) eqn:E.
    + inversion Hlookup; subst. apply in_or_app; left; exact Hin.
    + apply in_or_app; right. eapply IH; eassumption.
Qed.

Lemma lookup_rel_env_none_of_atoms : forall X rho,
  ~ In X (rel_env_atoms rho) -> lookup_rel_env X rho = None.
Proof.
  intros X rho; induction rho as [|e r IH]; simpl; intros H; [reflexivity|].
  destruct (Nat.eqb X (rel_env_name e)) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply H. simpl; auto.
  - apply IH. intro Hin; apply H; simpl; auto.
Qed.

Lemma lookup_rel_env_extend_neq : forall X Y e rho,
  rel_env_name e = X -> X <> Y -> lookup_rel_env Y (e :: rho) = lookup_rel_env Y rho.
Proof.
  intros X Y e rho Hname Hneq; simpl.
  assert (Nat.eqb Y (rel_env_name e) = false) by (apply Nat.eqb_neq; congruence).
  rewrite H; reflexivity.
Qed.

Lemma value_rel_world_open_ty_rec : forall T,
  forall rho e X inner outer v1 v2,
    lc_ty_at (S (length inner)) T ->
    rel_env_name e = X -> lookup_rel_env X rho = None ->
    ~ In X (ty_fvars T) ->
    (value_rel (e :: rho) (inner ++ outer)
       (open_ty_rec (length inner) (Ty_FVar X) T)
       (open_ty_rec (length inner) (Ty_FVar X) T) v1 v2 <->
     value_rel rho (inner ++ rel_env_rel e :: outer) T T v1 v2).
Proof.
  induction T; intros rho e X inner outer v1 v2 Hlc Hname Hnone Hfresh; simpl in *.
  - inversion Hlc; subst.
    destruct (Nat.eqb (length inner) n) eqn:E.
    + apply Nat.eqb_eq in E.
      assert (Hlookup : lookup_rel_env (rel_env_name e) (e :: rho) = Some e).
      { simpl. rewrite Nat.eqb_refl. reflexivity. }
      assert (Hnth : nth_error (inner ++ rel_env_rel e :: outer) n = Some (rel_env_rel e)).
      { rewrite nth_error_app2 by lia. rewrite E. replace (n-n) with 0 by lia. reflexivity. }
      split.
      * intros [e0 [_ [Hlook Hrel]]]. rewrite Hlookup in Hlook. inversion Hlook; subst e0.
        exists (rel_env_rel e); repeat split; try reflexivity; assumption.
      * intros [R [_ [Hnth' Hrel]]]. assert (R = rel_env_rel e).
        { rewrite Hnth in Hnth'. inversion Hnth'; reflexivity. }
        subst R. exists e; repeat split; try assumption; try reflexivity.
    + apply Nat.eqb_neq in E. assert (Hshort : n < length inner) by lia.
      assert (Hnthsame : nth_error (inner ++ outer) n = nth_error (inner ++ rel_env_rel e :: outer) n).
      { rewrite !nth_error_app1; try lia; reflexivity. }
      split.
      * intros [R [_ [Hnth Hrel]]]. exists R; repeat split; try reflexivity; try assumption.
        rewrite Hnthsame in Hnth. exact Hnth.
      * intros [R [_ [Hnth Hrel]]]. exists R; repeat split; try reflexivity; try assumption.
        rewrite <- Hnthsame in Hnth. exact Hnth.
  - assert (Hneq : a <> X).
    { intro Heq; subst. apply Hfresh. simpl; auto. }
    assert (E : Nat.eqb a (rel_env_name e) = false).
    { apply Nat.eqb_neq. congruence. }
    rewrite E. tauto.
  - inversion Hlc; subst.
    assert (Hf1 : ~ In (rel_env_name e) (ty_fvars T1)).
    { intro Hin; apply Hfresh; apply in_or_app; left; exact Hin. }
    assert (Hf2 : ~ In (rel_env_name e) (ty_fvars T2)).
    { intro Hin; apply Hfresh; apply in_or_app; right; exact Hin. }
    split.
    + intros [Hv1 [Hv2 Hfun]]. repeat split; try assumption.
      intros a1 a2 Hva1 Hva2 Ha.
      pose proof (proj2 (IHT1 rho e (rel_env_name e) inner outer a1 a2 H2 eq_refl Hnone Hf1) Ha) as Ha1.
      destruct (Hfun a1 a2 Hva1 Hva2 Ha1) as [w1 [w2 [Hm1 [Hm2 [Hw1 [Hw2 Hrel]]]]]].
      exists w1,w2; repeat split; try assumption.
      apply (proj1 (IHT2 rho e (rel_env_name e) inner outer w1 w2 H3 eq_refl Hnone Hf2)); exact Hrel.
    + intros [Hv1 [Hv2 Hfun]]. repeat split; try assumption.
      intros a1 a2 Hva1 Hva2 Ha.
      pose proof (proj1 (IHT1 rho e (rel_env_name e) inner outer a1 a2 H2 eq_refl Hnone Hf1) Ha) as Ha1.
      destruct (Hfun a1 a2 Hva1 Hva2 Ha1) as [w1 [w2 [Hm1 [Hm2 [Hw1 [Hw2 Hrel]]]]]].
      exists w1,w2; repeat split; try assumption.
      apply (proj2 (IHT2 rho e (rel_env_name e) inner outer w1 w2 H3 eq_refl Hnone Hf2)); exact Hrel.
  - inversion Hlc; subst.
    split.
    + intros [b1 [b2 [E1 [E2 [Hv1 [Hv2 Hfun]]]]]].
      exists b1,b2; repeat split; try assumption.
      intros U V R HwfU HwfV w1 w2 Hm1 Hm2 Hw1 Hw2.
      apply (proj1 (IHT rho e (rel_env_name e) (R :: inner) outer w1 w2 H1 eq_refl Hnone Hfresh)).
      exact (Hfun U V R HwfU HwfV w1 w2 Hm1 Hm2 Hw1 Hw2).
    + intros [b1 [b2 [E1 [E2 [Hv1 [Hv2 Hfun]]]]]].
      exists b1,b2; repeat split; try assumption.
      intros U V R HwfU HwfV w1 w2 Hm1 Hm2 Hw1 Hw2.
      apply (proj2 (IHT rho e (rel_env_name e) (R :: inner) outer w1 w2 H1 eq_refl Hnone Hfresh)).
      exact (Hfun U V R HwfU HwfV w1 w2 Hm1 Hm2 Hw1 Hw2).
  - tauto.
  - tauto.
Qed.

Lemma value_rel_extend_fresh : forall T1 T2 rho bs X e v1 v2,
  rel_env_name e = X -> lookup_rel_env X rho = None ->
  ~ In X (ty_fvars T1) -> ~ In X (ty_fvars T2) ->
  (value_rel rho bs T1 T2 v1 v2 <-> value_rel (e :: rho) bs T1 T2 v1 v2).
Proof.
  intros T1; induction T1; intros T2 rho bs X e v1 v2 Hname Hlookup Hfresh1 Hfresh2;
    destruct T2; simpl in *; try tauto.
  - assert (Hneq : a <> X).
    { intro Heq; subst. apply Hfresh1. simpl; auto. }
    split.
    + intros [e0 [Hxy [He Hrv]]]. exists e0; repeat split; try assumption.
      assert (E : Nat.eqb a (rel_env_name e) = false) by (apply Nat.eqb_neq; congruence).
      rewrite E; exact He.
    + intros [e0 [Hxy [He Hrv]]]. exists e0; repeat split; try assumption.
      simpl in He. assert (E : Nat.eqb a (rel_env_name e) = false) by (apply Nat.eqb_neq; congruence).
      rewrite E in He; exact He.
  - assert (Hfa : ~ In X (ty_fvars T1_1)).
    { intro Hin; apply Hfresh1; apply in_or_app; left; exact Hin. }
    assert (Hfb : ~ In X (ty_fvars T1_2)).
    { intro Hin; apply Hfresh1; apply in_or_app; right; exact Hin. }
    assert (Hfc : ~ In X (ty_fvars T2_1)).
    { intro Hin; apply Hfresh2; apply in_or_app; left; exact Hin. }
    assert (Hfd : ~ In X (ty_fvars T2_2)).
    { intro Hin; apply Hfresh2; apply in_or_app; right; exact Hin. }
    split.
    + intros [Hv1 [Hv2 Hfun]]. repeat split; try assumption.
      intros a1 a2 Hva1 Hva2 HaNew.
      pose proof (proj2 (IHT1_1 T2_1 rho bs X e a1 a2 Hname Hlookup Hfa Hfc) HaNew) as HaOld.
      destruct (Hfun a1 a2 Hva1 Hva2 HaOld) as [w1 [w2 [Hm1 [Hm2 [Hvw1 [Hvw2 Hrel]]]]]].
      exists w1, w2; repeat split; try assumption.
      apply (proj1 (IHT1_2 T2_2 rho bs X e w1 w2 Hname Hlookup Hfb Hfd)); exact Hrel.
    + intros [Hv1 [Hv2 Hfun]]. repeat split; try assumption.
      intros a1 a2 Hva1 Hva2 HaOld.
      pose proof (proj1 (IHT1_1 T2_1 rho bs X e a1 a2 Hname Hlookup Hfa Hfc) HaOld) as HaNew.
      destruct (Hfun a1 a2 Hva1 Hva2 HaNew) as [w1 [w2 [Hm1 [Hm2 [Hvw1 [Hvw2 Hrel]]]]]].
      exists w1, w2; repeat split; try assumption.
      apply (proj2 (IHT1_2 T2_2 rho bs X e w1 w2 Hname Hlookup Hfb Hfd)); exact Hrel.
  - split.
    + intros [b1 [b2 [E1 [E2 [Hv1 [Hv2 Hfun]]]]]].
      exists b1, b2; repeat split; try assumption.
      intros U V R HwfU HwfV w1 w2 Hm1 Hm2 Hvw1 Hvw2.
      apply (proj1 (IHT1 T2 rho (R :: bs) X e w1 w2 Hname Hlookup Hfresh1 Hfresh2)).
      exact (Hfun U V R HwfU HwfV w1 w2 Hm1 Hm2 Hvw1 Hvw2).
    + intros [b1 [b2 [E1 [E2 [Hv1 [Hv2 Hfun]]]]]].
      exists b1, b2; repeat split; try assumption.
      intros U V R HwfU HwfV w1 w2 Hm1 Hm2 Hvw1 Hvw2.
      apply (proj2 (IHT1 T2 rho (R :: bs) X e w1 w2 Hname Hlookup Hfresh1 Hfresh2)).
      exact (Hfun U V R HwfU HwfV w1 w2 Hm1 Hm2 Hvw1 Hvw2).
Qed.
Fixpoint lookup_term_subst (x : atom) (sigma : term_subst_env) : option (tm * tm) :=
  match sigma with
  | [] => None
  | (y, p) :: sigma' => if Nat.eqb x y then Some p else lookup_term_subst x sigma'
  end.
Fixpoint subst_term_left (sigma : term_subst_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => match lookup_term_subst x sigma with Some (a, _) => a | None => tm_fvar x end
  | tm_abs T b => tm_abs T (subst_term_left sigma b)
  | tm_app a b => tm_app (subst_term_left sigma a) (subst_term_left sigma b)
  | tm_tabs b => tm_tabs (subst_term_left sigma b)
  | tm_tapp a T => tm_tapp (subst_term_left sigma a) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if a b c => tm_if (subst_term_left sigma a) (subst_term_left sigma b) (subst_term_left sigma c)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (subst_term_left sigma a)
  | tm_natrec n b s => tm_natrec (subst_term_left sigma n) (subst_term_left sigma b) (subst_term_left sigma s)
  end.
Fixpoint subst_term_right (sigma : term_subst_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => match lookup_term_subst x sigma with Some (_, b) => b | None => tm_fvar x end
  | tm_abs T b => tm_abs T (subst_term_right sigma b)
  | tm_app a b => tm_app (subst_term_right sigma a) (subst_term_right sigma b)
  | tm_tabs b => tm_tabs (subst_term_right sigma b)
  | tm_tapp a T => tm_tapp (subst_term_right sigma a) T
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if a b c => tm_if (subst_term_right sigma a) (subst_term_right sigma b) (subst_term_right sigma c)
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (subst_term_right sigma a)
  | tm_natrec n b s => tm_natrec (subst_term_right sigma n) (subst_term_right sigma b) (subst_term_right sigma s)
  end.

Lemma subst_term_left_cons_unused : forall sigma x a b t,
  ~ In x (tm_fvars t) ->
  subst_term_left ((x, (a, b)) :: sigma) t = subst_term_left sigma t.
Proof.
  intros sigma x a b t; induction t; intros Hfresh; simpl in *.
  - reflexivity.
  - assert (Hneq : a0 <> x) by (intro Heq; apply Hfresh; simpl; auto).
    assert (E : Nat.eqb a0 x = false) by (apply Nat.eqb_neq; exact Hneq).
    simpl. rewrite E. destruct (lookup_term_subst a0 sigma); reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1. intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin.
    + apply IHt3. intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin.
  - reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin.
    + apply IHt3. intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin.
Qed.

Lemma subst_term_right_cons_unused : forall sigma x a b t,
  ~ In x (tm_fvars t) ->
  subst_term_right ((x, (a, b)) :: sigma) t = subst_term_right sigma t.
Proof.
  intros sigma x a b t; induction t; intros Hfresh; simpl in *.
  - reflexivity.
  - assert (Hneq : a0 <> x) by (intro Heq; apply Hfresh; simpl; auto).
    assert (E : Nat.eqb a0 x = false) by (apply Nat.eqb_neq; exact Hneq).
    simpl. rewrite E. destruct (lookup_term_subst a0 sigma); reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal. apply IHt. exact Hfresh.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1. intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin.
    + apply IHt3. intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin.
  - reflexivity.
  - f_equal. apply IHt. exact Hfresh.
  - f_equal.
    + apply IHt1. intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt2. intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin.
    + apply IHt3. intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin.
Qed.

Definition plug_left (rho : rel_env) (sigma : term_subst_env) (t : tm) :=
  subst_term_left sigma (subst_tm_ty_rel_left rho t).
Definition plug_right (rho : rel_env) (sigma : term_subst_env) (t : tm) :=
  subst_term_right sigma (subst_tm_ty_rel_right rho t).

Lemma subst_tm_ty_rel_left_open_tm_rec : forall rho k u t,
  subst_tm_ty_rel_left rho (open_tm_rec k u t) =
  open_tm_rec k (subst_tm_ty_rel_left rho u) (subst_tm_ty_rel_left rho t).
Proof.
  intros rho k u t; revert k u; induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
Qed.

Lemma subst_tm_ty_rel_right_open_tm_rec : forall rho k u t,
  subst_tm_ty_rel_right rho (open_tm_rec k u t) =
  open_tm_rec k (subst_tm_ty_rel_right rho u) (subst_tm_ty_rel_right rho t).
Proof.
  intros rho k u t; revert k u; induction t; intros k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
Qed.


Definition rel_env_lc (rho : rel_env) : Prop :=
  forall X e, lookup_rel_env X rho = Some e ->
    lc_ty_at 0 (rel_env_left_ty e) /\ lc_ty_at 0 (rel_env_right_ty e).

Lemma open_ty_rec_lc_early : forall K k U T,
  lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  intros K k U T Hlc HKK'; revert k HKK'.
  induction Hlc; intros k' Hkk'; simpl; try reflexivity.
  - assert (E : Nat.eqb k' i = false) by (apply Nat.eqb_neq; lia).
    rewrite E; reflexivity.
  - f_equal; [apply IHHlc1|apply IHHlc2]; assumption.
  - f_equal. apply IHHlc. lia.
Qed.

Lemma subst_ty_rel_left_open_rec : forall rho e X k T,
  rel_env_lc rho -> rel_env_name e = X -> lookup_rel_env X rho = None ->
  ~ In X (ty_fvars T) ->
  subst_ty_rel_left (e :: rho) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k (rel_env_left_ty e) (subst_ty_rel_left rho T).
Proof.
  intros rho e X k T Hr Hname Hnone Hfresh; revert k.
  induction T; intros k; simpl in *.
  - destruct (Nat.eqb k n); simpl; [|reflexivity].
    assert (E : Nat.eqb X (rel_env_name e) = true) by (apply Nat.eqb_eq; symmetry; exact Hname).
    rewrite E; reflexivity.
  - assert (Hneq : X <> a).
    { intro H; subst. apply Hfresh; simpl; auto. }
    assert (Eneq : Nat.eqb a (rel_env_name e) = false) by (apply Nat.eqb_neq; congruence).
    rewrite Eneq.
    destruct (lookup_rel_env a rho) as [e0|] eqn:E.
    + destruct (Hr a e0 E) as [Hty _].
      symmetry. eapply open_ty_rec_lc_early; [exact Hty|lia].
    + reflexivity.
  - f_equal.
    + apply IHT1; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHT2; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal. apply IHT; assumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_ty_rel_right_open_rec : forall rho e X k T,
  rel_env_lc rho -> rel_env_name e = X -> lookup_rel_env X rho = None ->
  ~ In X (ty_fvars T) ->
  subst_ty_rel_right (e :: rho) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k (rel_env_right_ty e) (subst_ty_rel_right rho T).
Proof.
  intros rho e X k T Hr Hname Hnone Hfresh; revert k.
  induction T; intros k; simpl in *.
  - destruct (Nat.eqb k n); simpl; [|reflexivity].
    assert (E : Nat.eqb X (rel_env_name e) = true) by (apply Nat.eqb_eq; symmetry; exact Hname).
    rewrite E; reflexivity.
  - assert (Hneq : X <> a).
    { intro H; subst. apply Hfresh; simpl; auto. }
    assert (Eneq : Nat.eqb a (rel_env_name e) = false) by (apply Nat.eqb_neq; congruence).
    rewrite Eneq.
    destruct (lookup_rel_env a rho) as [e0|] eqn:E.
    + destruct (Hr a e0 E) as [_ Hty].
      symmetry. eapply open_ty_rec_lc_early; [exact Hty|lia].
    + reflexivity.
  - f_equal.
    + apply IHT1; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHT2; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal. apply IHT; assumption.
  - reflexivity.
  - reflexivity.
Qed.

Lemma subst_tm_ty_rel_left_open_rec : forall rho e X k t,
  rel_env_lc rho -> rel_env_name e = X -> lookup_rel_env X rho = None ->
  ~ In X (tm_ty_fvars t) ->
  subst_tm_ty_rel_left (e :: rho) (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k (rel_env_left_ty e) (subst_tm_ty_rel_left rho t).
Proof.
  intros rho e X k t Hr Hname Hnone Hfresh; revert k.
  induction t; intros k; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + eapply subst_ty_rel_left_open_rec; eauto.
      intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt2; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + eapply subst_ty_rel_left_open_rec; eauto.
      intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt2; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin.
    + apply IHt3; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin.
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt1; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt2; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin.
    + apply IHt3; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin.
Qed.

Lemma subst_tm_ty_rel_right_open_rec : forall rho e X k t,
  rel_env_lc rho -> rel_env_name e = X -> lookup_rel_env X rho = None ->
  ~ In X (tm_ty_fvars t) ->
  subst_tm_ty_rel_right (e :: rho) (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k (rel_env_right_ty e) (subst_tm_ty_rel_right rho t).
Proof.
  intros rho e X k t Hr Hname Hnone Hfresh; revert k.
  induction t; intros k; simpl in *.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + eapply subst_ty_rel_right_open_rec; eauto.
      intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal.
    + apply IHt1; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt2; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + eapply subst_ty_rel_right_open_rec; eauto.
      intro Hin; apply Hfresh; apply in_or_app; right; exact Hin.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply IHt1; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt2; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin.
    + apply IHt3; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin.
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal.
    + apply IHt1; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; left; exact Hin.
    + apply IHt2; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; left; exact Hin.
    + apply IHt3; try assumption.
      intro Hin; apply Hfresh; apply in_or_app; right; apply in_or_app; right; exact Hin.
Qed.

Lemma lc_tm_at_weaken : forall K k k' t,
  k <= k' -> lc_tm_at K k t -> lc_tm_at K k' t.
Proof.
  intros K k k' t Hkk' Hlc; revert k' Hkk'.
  induction Hlc; intros k' Hkk'.
  - apply lc_tm_bvar; lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; [assumption|apply IHHlc; lia].
  - apply lc_tm_app; [apply IHHlc1|apply IHHlc2]; assumption.
  - apply lc_tm_tabs; apply IHHlc; assumption.
  - apply lc_tm_tapp; [apply IHHlc; assumption|assumption].
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; assumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ; apply IHHlc; assumption.
  - apply lc_tm_rec; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; assumption.
Qed.

Lemma lc_ty_at_weaken : forall K K' T,
  K <= K' -> lc_ty_at K T -> lc_ty_at K' T.
Proof.
  intros K K' T Hle Hlc; revert K' Hle.
  induction Hlc; intros K' Hle.
  - constructor; lia.
  - constructor.
  - constructor; [apply IHHlc1|apply IHHlc2]; assumption.
  - apply lc_ty_all. apply IHHlc. lia.
  - constructor.
  - constructor.
Qed.

Lemma lc_tm_at_weaken_K : forall K K' k t,
  K <= K' -> lc_tm_at K k t -> lc_tm_at K' k t.
Proof.
  intros K K' k t Hle Hlc; revert K' Hle.
  induction Hlc; intros K' Hle.
  - apply lc_tm_bvar; assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs; [eapply lc_ty_at_weaken; eauto|apply IHHlc; assumption].
  - apply lc_tm_app; [apply IHHlc1|apply IHHlc2]; assumption.
  - apply lc_tm_tabs; apply IHHlc; lia.
  - apply lc_tm_tapp; [apply IHHlc; assumption|eapply lc_ty_at_weaken; eauto].
  - apply lc_tm_true.
  - apply lc_tm_false.
  - apply lc_tm_if; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; assumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ; apply IHHlc; assumption.
  - apply lc_tm_rec; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; assumption.
Qed.

Lemma subst_ty_rel_left_lc : forall rho K T,
  rel_env_lc rho -> lc_ty_at K T -> lc_ty_at K (subst_ty_rel_left rho T).
Proof.
  intros rho K T Hr Hlc; revert K Hlc; induction T; intros K Hlc; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - destruct (lookup_rel_env a rho) as [e|] eqn:E.
    + destruct (Hr a e E) as [Hleft _].
      eapply lc_ty_at_weaken with (K:=0) (K':=K); [lia|exact Hleft].
    + constructor.
  - inversion Hlc; subst. constructor; [apply IHT1|apply IHT2]; assumption.
  - inversion Hlc; subst. apply lc_ty_all. apply IHT. assumption.
  - constructor.
  - constructor.
Qed.

Lemma subst_ty_rel_right_lc : forall rho K T,
  rel_env_lc rho -> lc_ty_at K T -> lc_ty_at K (subst_ty_rel_right rho T).
Proof.
  intros rho K T Hr Hlc; revert K Hlc; induction T; intros K Hlc; simpl in *.
  - inversion Hlc; subst. constructor; assumption.
  - destruct (lookup_rel_env a rho) as [e|] eqn:E.
    + destruct (Hr a e E) as [_ Hright].
      eapply lc_ty_at_weaken with (K:=0) (K':=K); [lia|exact Hright].
    + constructor.
  - inversion Hlc; subst. constructor; [apply IHT1|apply IHT2]; assumption.
  - inversion Hlc; subst. apply lc_ty_all. apply IHT. assumption.
  - constructor.
  - constructor.
Qed.

Lemma subst_tm_ty_rel_left_lc : forall rho K k t,
  rel_env_lc rho -> lc_tm_at K k t -> lc_tm_at K k (subst_tm_ty_rel_left rho t).
Proof.
  intros rho K k t Hr Hlc; induction Hlc; simpl.
  - constructor; assumption.
  - constructor.
  - apply lc_tm_abs; [eapply subst_ty_rel_left_lc|]; eauto.
  - econstructor; eauto.
  - apply lc_tm_tabs. eauto.
  - apply lc_tm_tapp; [eauto|eapply subst_ty_rel_left_lc]; eauto.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - constructor.
  - constructor; eauto.
  - econstructor; eauto.
Qed.

Lemma subst_tm_ty_rel_right_lc : forall rho K k t,
  rel_env_lc rho -> lc_tm_at K k t -> lc_tm_at K k (subst_tm_ty_rel_right rho t).
Proof.
  intros rho K k t Hr Hlc; induction Hlc; simpl.
  - constructor; assumption.
  - constructor.
  - apply lc_tm_abs; [eapply subst_ty_rel_right_lc|]; eauto.
  - econstructor; eauto.
  - apply lc_tm_tabs. eauto.
  - apply lc_tm_tapp; [eauto|eapply subst_ty_rel_right_lc]; eauto.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - constructor.
  - constructor; eauto.
  - econstructor; eauto.
Qed.

Lemma subst_term_left_lc : forall sigma K k t,
  (forall x a b, lookup_term_subst x sigma = Some (a, b) -> lc_tm_at 0 0 a) ->
  lc_tm_at K k t -> lc_tm_at K k (subst_term_left sigma t).
Proof.
  intros sigma K k t Hsigma Hlc; induction Hlc; simpl.
  - constructor; assumption.
  - destruct (lookup_term_subst x sigma) as [[a b]|] eqn:E.
    + eapply lc_tm_at_weaken with (k:=0); [lia|].
      eapply (lc_tm_at_weaken_K 0 K 0 a); [lia|apply Hsigma with (x:=x) (b:=b); exact E].
    + constructor.
  - apply lc_tm_abs; assumption.
  - econstructor; eauto.
  - apply lc_tm_tabs; assumption.
  - apply lc_tm_tapp; assumption.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - constructor.
  - constructor; assumption.
  - econstructor; eauto.
Qed.

Lemma subst_term_right_lc : forall sigma K k t,
  (forall x a b, lookup_term_subst x sigma = Some (a, b) -> lc_tm_at 0 0 b) ->
  lc_tm_at K k t -> lc_tm_at K k (subst_term_right sigma t).
Proof.
  intros sigma K k t Hsigma Hlc; induction Hlc; simpl.
  - constructor; assumption.
  - destruct (lookup_term_subst x sigma) as [[a b]|] eqn:E.
    + eapply lc_tm_at_weaken with (k:=0); [lia|].
      eapply (lc_tm_at_weaken_K 0 K 0 b); [lia|apply Hsigma with (x:=x) (a:=a); exact E].
    + constructor.
  - apply lc_tm_abs; assumption.
  - econstructor; eauto.
  - apply lc_tm_tabs; assumption.
  - apply lc_tm_tapp; assumption.
  - constructor.
  - constructor.
  - econstructor; eauto.
  - constructor.
  - constructor; assumption.
  - econstructor; eauto.
Qed.

Lemma plug_left_lc : forall rho sigma t,
  rel_env_lc rho ->
  (forall x a b, lookup_term_subst x sigma = Some (a, b) -> lc_tm_at 0 0 a) ->
  lc_tm_at 0 0 t -> lc_tm_at 0 0 (plug_left rho sigma t).
Proof. intros; unfold plug_left; eapply subst_term_left_lc; eauto using subst_tm_ty_rel_left_lc. Qed.

Lemma plug_right_lc : forall rho sigma t,
  rel_env_lc rho ->
  (forall x a b, lookup_term_subst x sigma = Some (a, b) -> lc_tm_at 0 0 b) ->
  lc_tm_at 0 0 t -> lc_tm_at 0 0 (plug_right rho sigma t).
Proof. intros; unfold plug_right; eapply subst_term_right_lc; eauto using subst_tm_ty_rel_right_lc. Qed.

Definition rel_env_wf (Delta : ty_context) (rho : rel_env) : Prop :=
  forall X, In X Delta -> exists e,
    lookup_rel_env X rho = Some e /\
    locally_closed_ty (rel_env_left_ty e) /\ locally_closed_ty (rel_env_right_ty e).

Definition term_env_related (rho : rel_env) (Gamma : context)
    (sigma : term_subst_env) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    exists a b, lookup_term_subst x sigma = Some (a, b) /\
      value a /\ value b /\ value_rel rho [] T T a b.

Definition term_env_lc (sigma : term_subst_env) : Prop :=
  forall x a b, lookup_term_subst x sigma = Some (a, b) ->
    lc_tm_at 0 0 a /\ lc_tm_at 0 0 b.

Lemma term_env_lc_extend : forall sigma x a b,
  term_env_lc sigma -> locally_closed_tm a -> locally_closed_tm b ->
  term_env_lc ((x, (a, b)) :: sigma).
Proof.
  intros sigma x a b Henv Ha Hb y a' b' Hlook.
  simpl in Hlook. destruct (Nat.eqb y x) eqn:E.
  - inversion Hlook; subst. split; [exact Ha|exact Hb].
  - eapply Henv; eassumption.
Qed.

Lemma term_env_related_extend : forall rho Gamma sigma x T a b,
  term_env_related rho Gamma sigma ->
  value a -> value b -> value_rel rho [] T T a b ->
  term_env_related rho (update Gamma x T) ((x, (a, b)) :: sigma).
Proof.
  intros rho Gamma sigma x T a b Henv Ha Hb Hrel y S Hlook.
  unfold term_env_related in *.
  simpl in Hlook. destruct (Nat.eqb y x) eqn:E.
  - inversion Hlook; subst S.
    exists a, b; simpl. rewrite E. repeat split; assumption.
  - destruct (Henv y S Hlook) as [a' [b' [Hsub [Hva [Hvb Hrel']]]]].
    exists a', b'; simpl. rewrite E. repeat split; assumption.
Qed.

Lemma rel_env_lc_extend : forall rho X U V R,
  rel_env_lc rho -> locally_closed_ty U -> locally_closed_ty V ->
  rel_env_lc
    ({| rel_env_name := X; rel_env_left_ty := U;
        rel_env_right_ty := V; rel_env_rel := R |} :: rho).
Proof.
  intros rho X U V R Hr HwfU HwfV Y e Hlook.
  simpl in Hlook. destruct (Nat.eqb Y X) eqn:E.
  - inversion Hlook; subst e. split; assumption.
  - specialize (Hr Y e Hlook) as H; exact H.
Qed.

Lemma term_env_related_world : forall rho Gamma sigma X e,
  rel_env_name e = X -> lookup_rel_env X rho = None ->
  (forall x T, lookup_context x Gamma = Some T -> ~ In X (ty_fvars T)) ->
  term_env_related rho Gamma sigma -> term_env_related (e :: rho) Gamma sigma.
Proof.
  intros rho Gamma sigma X e Hname Hnone Hfresh Henv x T Hlookup.
  destruct (Henv x T Hlookup) as [a [b [Hsub [Ha [Hb Hrel]]]]].
  exists a, b; repeat split; try assumption.
  eapply (proj1 (value_rel_extend_fresh T T rho [] X e a b Hname Hnone
    (Hfresh x T Hlookup) (Hfresh x T Hlookup))); exact Hrel.
Qed.

Lemma open_tm_rec_lc : forall K k k' u t,
  lc_tm_at K k t -> k <= k' -> open_tm_rec k' u t = t.
Proof.
  intros K k k' u t Hlc; revert k'.
  induction Hlc; intros k' Hkk'; simpl; try reflexivity.
  - assert (E : Nat.eqb k' i = false) by (apply Nat.eqb_neq; lia).
    rewrite E; reflexivity.
  - f_equal. apply IHHlc. lia.
  - f_equal; [apply IHHlc1|apply IHHlc2]; lia.
  - f_equal. apply IHHlc. assumption.
  - f_equal. apply IHHlc. assumption.
  - f_equal; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; assumption.
  - f_equal. apply IHHlc. assumption.
  - f_equal; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; assumption.
Qed.

Lemma open_ty_rec_lc : forall K k U T,
  lc_ty_at K T -> K <= k -> open_ty_rec k U T = T.
Proof.
  intros K k U T Hlc Hkk'; revert k Hkk'.
  induction Hlc; intros k' Hkk'; simpl; try reflexivity.
  - assert (E : Nat.eqb k' i = false) by (apply Nat.eqb_neq; lia).
    rewrite E; reflexivity.
  - f_equal; [apply IHHlc1|apply IHHlc2]; assumption.
  - f_equal. apply IHHlc. lia.
Qed.

Lemma open_tm_ty_rec_lc : forall K K' k U t,
  lc_tm_at K k t -> K <= K' -> open_tm_ty_rec K' U t = t.
Proof.
  intros K K' k U t Hlc HKK'; revert K' HKK'; induction Hlc; intros K' HKK'; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + eapply open_ty_rec_lc; eauto.
    + apply IHHlc; assumption.
  - f_equal; [apply IHHlc1|apply IHHlc2]; assumption.
  - f_equal. apply IHHlc. lia.
  - f_equal.
    + apply IHHlc; assumption.
    + eapply open_ty_rec_lc; eauto.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; assumption.
  - reflexivity.
  - f_equal. apply IHHlc; assumption.
  - f_equal; [apply IHHlc1|apply IHHlc2|apply IHHlc3]; assumption.
Qed.

Lemma subst_term_left_open_rec : forall sigma k t u,
  (forall x a b, lookup_term_subst x sigma = Some (a, b) -> locally_closed_tm a) ->
  subst_term_left sigma (open_tm_rec k u t) =
  open_tm_rec k (subst_term_left sigma u) (subst_term_left sigma t).
Proof.
  intros sigma k t; revert k; induction t; intros k u Hlc; simpl.
  - destruct (Nat.eqb k n); simpl; reflexivity.
  - destruct (lookup_term_subst a sigma) as [[a1 a2]|] eqn:E; simpl.
    + unfold locally_closed_tm in Hlc. specialize (Hlc a a1 a2 E).
      rewrite (open_tm_rec_lc 0 0 k (subst_term_left sigma u) a1 Hlc (Nat.le_0_l _)); reflexivity.
    + reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
Qed.

Lemma subst_term_left_open : forall sigma t u,
  (forall x a b, lookup_term_subst x sigma = Some (a, b) -> locally_closed_tm a) ->
  subst_term_left sigma (open_tm t u) =
  open_tm (subst_term_left sigma t) (subst_term_left sigma u).
Proof. intros sigma t u Hlc; unfold open_tm; eapply subst_term_left_open_rec; eauto. Qed.

Lemma subst_term_right_open_rec : forall sigma k t u,
  (forall x a b, lookup_term_subst x sigma = Some (a, b) -> locally_closed_tm b) ->
  subst_term_right sigma (open_tm_rec k u t) =
  open_tm_rec k (subst_term_right sigma u) (subst_term_right sigma t).
Proof.
  intros sigma k t; revert k; induction t; intros k u Hlc; simpl.
  - destruct (Nat.eqb k n); simpl; reflexivity.
  - destruct (lookup_term_subst a sigma) as [[a1 a2]|] eqn:E; simpl.
    + unfold locally_closed_tm in Hlc. specialize (Hlc a a1 a2 E).
      rewrite (open_tm_rec_lc 0 0 k (subst_term_right sigma u) a2 Hlc (Nat.le_0_l _)); reflexivity.
    + reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
Qed.

Lemma plug_left_open_rec : forall rho sigma k u t,
  (forall x a b, lookup_term_subst x sigma = Some (a, b) -> locally_closed_tm a) ->
  plug_left rho sigma (open_tm_rec k u t) =
  open_tm_rec k (plug_left rho sigma u) (plug_left rho sigma t).
Proof.
  intros; unfold plug_left.
  rewrite subst_tm_ty_rel_left_open_tm_rec.
  apply subst_term_left_open_rec; assumption.
Qed.

Lemma plug_right_open_rec : forall rho sigma k u t,
  (forall x a b, lookup_term_subst x sigma = Some (a, b) -> locally_closed_tm b) ->
  plug_right rho sigma (open_tm_rec k u t) =
  open_tm_rec k (plug_right rho sigma u) (plug_right rho sigma t).
Proof.
  intros; unfold plug_right.
  rewrite subst_tm_ty_rel_right_open_tm_rec.
  apply subst_term_right_open_rec; assumption.
Qed.

Lemma subst_term_right_open : forall sigma t u,
  (forall x a b, lookup_term_subst x sigma = Some (a, b) -> locally_closed_tm b) ->
  subst_term_right sigma (open_tm t u) =
  open_tm (subst_term_right sigma t) (subst_term_right sigma u).
Proof.
  intros sigma t u Hlc; unfold open_tm; eapply subst_term_right_open_rec; eauto.
Qed.

Lemma subst_term_left_open_ty : forall sigma t U,
  (forall x a b, lookup_term_subst x sigma = Some (a, b) -> locally_closed_tm a) ->
  subst_term_left sigma (open_tm_ty t U) =
  open_tm_ty (subst_term_left sigma t) U.
Proof.
  intros sigma t U Hlc; unfold open_tm_ty.
  revert U; generalize 0 as k.
  induction t; intros k U; simpl.
  - reflexivity.
  - destruct (lookup_term_subst a sigma) as [[a1 a2]|] eqn:E; simpl; try reflexivity.
    unfold locally_closed_tm in Hlc. specialize (Hlc a a1 a2 E).
    rewrite (open_tm_ty_rec_lc 0 k 0 U a1 Hlc (Nat.le_0_l _)); reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
Qed.

Lemma subst_term_right_open_ty : forall sigma t U,
  (forall x a b, lookup_term_subst x sigma = Some (a, b) -> locally_closed_tm b) ->
  subst_term_right sigma (open_tm_ty t U) =
  open_tm_ty (subst_term_right sigma t) U.
Proof.
  intros sigma t U Hlc; unfold open_tm_ty.
  revert U; generalize 0 as k.
  induction t; intros k U; simpl.
  - reflexivity.
  - destruct (lookup_term_subst a sigma) as [[a1 a2]|] eqn:E; simpl; try reflexivity.
    unfold locally_closed_tm in Hlc. specialize (Hlc a a1 a2 E).
    rewrite (open_tm_ty_rec_lc 0 k 0 U a2 Hlc (Nat.le_0_l _)); reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2].
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3].
Qed.

Lemma subst_term_left_open_ty_rec : forall sigma k U t,
  term_env_lc sigma ->
  subst_term_left sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (subst_term_left sigma t).
Proof.
  intros sigma k U t Hlc; revert k U Hlc; induction t; intros k U Hlc; simpl.
  - reflexivity.
  - destruct (lookup_term_subst a sigma) as [[u1 u2]|] eqn:E; simpl; [|reflexivity].
    destruct (Hlc a u1 u2 E) as [Ha _].
    unfold locally_closed_tm in Ha.
    rewrite (open_tm_ty_rec_lc 0 k 0 U u1 Ha (Nat.le_0_l k)); reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
Qed.

Lemma subst_term_right_open_ty_rec : forall sigma k U t,
  term_env_lc sigma ->
  subst_term_right sigma (open_tm_ty_rec k U t) =
  open_tm_ty_rec k U (subst_term_right sigma t).
Proof.
  intros sigma k U t Hlc; revert k U Hlc; induction t; intros k U Hlc; simpl.
  - reflexivity.
  - destruct (lookup_term_subst a sigma) as [[u1 u2]|] eqn:E; simpl; [|reflexivity].
    destruct (Hlc a u1 u2 E) as [_ Hb].
    unfold locally_closed_tm in Hb.
    rewrite (open_tm_ty_rec_lc 0 k 0 U u2 Hb (Nat.le_0_l k)); reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2]; assumption.
  - f_equal. apply IHt; assumption.
  - f_equal. apply IHt; assumption.
  - reflexivity.
  - reflexivity.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
  - reflexivity.
  - f_equal. apply IHt; assumption.
  - f_equal; [apply IHt1|apply IHt2|apply IHt3]; assumption.
Qed.

Lemma plug_left_type_open_rec : forall rho e X sigma k t,
  rel_env_lc rho -> rel_env_name e = X -> lookup_rel_env X rho = None ->
  term_env_lc sigma ->
  ~ In X (tm_ty_fvars t) ->
  plug_left (e :: rho) sigma (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k (rel_env_left_ty e) (plug_left rho sigma t).
Proof.
  intros rho e X sigma k t Hr Hname Hnone Hsigma Hfresh.
  unfold plug_left. rewrite subst_tm_ty_rel_left_open_rec; eauto.
  apply subst_term_left_open_ty_rec; exact Hsigma.
Qed.

Lemma plug_right_type_open_rec : forall rho e X sigma k t,
  rel_env_lc rho -> rel_env_name e = X -> lookup_rel_env X rho = None ->
  term_env_lc sigma ->
  ~ In X (tm_ty_fvars t) ->
  plug_right (e :: rho) sigma (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k (rel_env_right_ty e) (plug_right rho sigma t).
Proof.
  intros rho e X sigma k t Hr Hname Hnone Hsigma Hfresh.
  unfold plug_right. rewrite subst_tm_ty_rel_right_open_rec; eauto.
  apply subst_term_right_open_ty_rec; exact Hsigma.
Qed.

Lemma multi_app_left : forall t t' u,
  multi t t' -> locally_closed_tm u -> multi (tm_app t u) (tm_app t' u).
Proof.
  intros t t' u H; induction H; intros Hlc.
  - constructor.
  - econstructor; [eapply ST_App1; eassumption|apply IHmulti; assumption].
Qed.

Lemma multi_app_right : forall v t t',
  value v -> multi t t' -> multi (tm_app v t) (tm_app v t').
Proof.
  intros v t t' Hv H; induction H.
  - constructor.
  - econstructor; [eapply ST_App2; eassumption|exact IHmulti].
Qed.

Lemma multi_tapp_ctx : forall t t' U,
  multi t t' -> locally_closed_ty U -> multi (tm_tapp t U) (tm_tapp t' U).
Proof.
  intros t t' U H; induction H; intros Hwf.
  - constructor.
  - econstructor; [eapply ST_TApp; eassumption|apply IHmulti; assumption].
Qed.

Lemma multi_succ_ctx : forall t t', multi t t' -> multi (tm_succ t) (tm_succ t').
Proof.
  intros t t' H; induction H.
  - constructor.
  - econstructor; [eapply ST_Succ; eassumption|exact IHmulti].
Qed.

Lemma multi_if_ctx : forall c c' t e,
  multi c c' -> locally_closed_tm t -> locally_closed_tm e ->
  multi (tm_if c t e) (tm_if c' t e).
Proof.
  intros c c' t e H; induction H; intros Ht He.
  - constructor.
  - econstructor; [eapply ST_If; eassumption|apply IHmulti; assumption].
Qed.

Lemma multi_rec_arg_ctx : forall n n' b s,
  multi n n' -> locally_closed_tm b -> locally_closed_tm s ->
  multi (tm_natrec n b s) (tm_natrec n' b s).
Proof.
  intros n n' b s H; induction H; intros Hb Hs.
  - constructor.
  - econstructor; [eapply ST_RecArg; eassumption|apply IHmulti; assumption].
Qed.

Lemma multi_rec_base_ctx : forall n b b' s,
  numeric_value n -> multi b b' -> locally_closed_tm s ->
  multi (tm_natrec n b s) (tm_natrec n b' s).
Proof.
  intros n b b' s Hn H; induction H; intros Hs.
  - constructor.
  - econstructor; [eapply ST_RecBase; eassumption|apply IHmulti; assumption].
Qed.

Lemma multi_rec_step_ctx : forall n b s s',
  numeric_value n -> value b -> multi s s' ->
  multi (tm_natrec n b s) (tm_natrec n b s').
Proof.
  intros n b s s' Hn Hb H; induction H.
  - constructor.
  - econstructor; [eapply ST_RecStep; eassumption|exact IHmulti].
Qed.

Lemma rel_env_wf_extend : forall Delta rho X e,
  rel_env_wf Delta rho -> ~ In X Delta -> rel_env_name e = X ->
  locally_closed_ty (rel_env_left_ty e) -> locally_closed_ty (rel_env_right_ty e) ->
  rel_env_wf (X :: Delta) (e :: rho).
Proof.
  intros Delta rho X e Hwf Hfresh Hname HU HV Y Hin.
  simpl in Hin. destruct Hin as [<-|Hin].
  - exists e. split.
    + simpl. rewrite Hname, Nat.eqb_refl. reflexivity.
    + auto.
  - destruct (Hwf Y Hin) as [e' [Hlook [Hleft Hright]]].
    exists e'. split.
    + simpl. assert (Nat.eqb Y (rel_env_name e) = false).
      { apply Nat.eqb_neq. rewrite Hname. intro Heq; subst; contradiction. }
      rewrite H. exact Hlook.
    + auto.
Qed.



Lemma open_ty_lc_at : forall T K U,
  lc_ty_at (S K) T -> lc_ty_at K U ->
  lc_ty_at K (open_ty_rec K U T).
Proof.
  induction T; intros K U Ht Hu; simpl.
  - inversion Ht; subst. destruct (Nat.eqb K n) eqn:E.
    + exact Hu.
    + constructor. apply Nat.eqb_neq in E. lia.
  - constructor.
  - inversion Ht; subst. constructor; [eapply IHT1|eapply IHT2]; eassumption.
  - inversion Ht; subst. constructor.
    eapply IHT. eassumption. eapply lc_ty_at_weaken with (K:=K) (K':=S K); eauto; lia.
  - constructor.
  - constructor.
Qed.

Lemma has_type_ty_lc : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T Hty; induction Hty.
  - eapply wf_ty_lc; eassumption.
  - constructor; [eapply wf_ty_lc; eassumption|].
    specialize (H1 (fresh_atom L) (fresh_atom_notin L)). exact H1.
  - inversion IHHty1; assumption.
  - apply lc_ty_all.
    pose proof (H0 (fresh_atom L) (fresh_atom_notin L)) as Hopened.
    eapply lc_ty_open_inv; exact Hopened.
  - inversion IHHty; subst. eapply open_ty_lc_at; [eassumption|eapply wf_ty_lc; eassumption].
  - constructor.
  - constructor.
  - exact IHHty2.
  - constructor.
  - constructor.
  - exact IHHty2.
Qed.

Lemma step_deterministic : forall t u1 u2, t --> u1 -> t --> u2 -> u1 = u2.
Proof.
  intros t u1 u2 H1; revert u2; induction H1; intros u2 H2;
    inversion H2; subst; try reflexivity; try congruence;
    try solve [exfalso; eapply value_no_step; eauto];
    try solve [exfalso; eapply numeric_value_no_step; eauto];
    try solve [f_equal; eauto].
  all: try solve [congruence].
  all: try solve [f_equal; eauto].
  all: try solve [exfalso; eapply value_no_step; eauto].
  all: try solve [exfalso; eapply numeric_value_no_step; eauto].
  all: try solve [exfalso; match goal with
    | Hs : tm_abs ?A ?b --> ?u, Hlc : locally_closed_tm (tm_abs ?A ?b) |- _ =>
        exact (value_no_step _ _ (v_abs _ _ Hlc) Hs)
    | Hs : tm_tabs ?b --> ?u, Hlc : locally_closed_tm (tm_tabs ?b) |- _ =>
        exact (value_no_step _ _ (v_tabs _ Hlc) Hs)
    | Hs : ?v --> ?u, Hv : value ?v |- _ => exact (value_no_step _ _ Hv Hs)
    | Hs : ?n --> ?u, Hn : numeric_value ?n |- _ => exact (numeric_value_no_step _ _ Hn Hs)
    | Hs : tm_zero --> ?u |- _ => exact (numeric_value_no_step _ _ nv_zero Hs)
    | Hs : tm_true --> ?u |- _ => exact (value_no_step _ _ v_true Hs)
    | Hs : tm_false --> ?u |- _ => exact (value_no_step _ _ v_false Hs)
    | Hs : tm_succ ?n --> ?u, Hn : numeric_value ?n |- _ =>
        exact (numeric_value_no_step _ _ (nv_succ n Hn) Hs)
    | Hs : tm_if tm_true ?a ?b --> ?u |- _ => exact (value_no_step _ _ v_true Hs)
    | Hs : tm_if tm_false ?a ?b --> ?u |- _ => exact (value_no_step _ _ v_false Hs)
    end].
Qed.

Lemma multi_value_unique : forall t v1 v2,
  multi t v1 -> value v1 -> multi t v2 -> value v2 -> v1 = v2.
Proof.
  intros t v1 v2 H1; revert v2.
  induction H1 as [x|x y z Hxy Hyz IH]; intros v2 Hv1 H2 Hv2.
  - inversion H2 as [|x' y' z' Hstep Hmulti]; subst.
    + reflexivity.
    + exfalso. exact (value_no_step x y' Hv1 Hstep).
  - inversion H2 as [|x' y' z' Hstep Hmulti]; subst.
    + exfalso. eapply value_no_step; eauto.
    + assert (y = y') by (eapply step_deterministic; eassumption). subst y'.
      eapply IH; eassumption.
Qed.

Theorem fundamental : forall Delta Gamma t T,
  has_type Delta Gamma t T ->
  forall rho sigma,
    rel_env_wf Delta rho -> rel_env_lc rho ->
    term_env_related rho Gamma sigma -> term_env_lc sigma ->
    exists v1 v2,
      multi (plug_left rho sigma t) v1 /\
      multi (plug_right rho sigma t) v2 /\
      value v1 /\ value v2 /\ value_rel rho [] T T v1 v2.
Proof.
  intros Delta Gamma t T Hty; induction Hty; intros rho sigma Hrwf Hrlc Htr Hslc.
  - destruct (Htr x T H) as [a [b [Hsub [Ha [Hb Hrel]]]]].
    exists a,b. split; [unfold plug_left; simpl; rewrite Hsub; constructor|].
    split; [unfold plug_right; simpl; rewrite Hsub; constructor|].
    repeat split; assumption.
  - set (sL := subst_tm_ty_rel_left rho t2).
    set (sR := subst_tm_ty_rel_right rho t2).
    set (X := fresh_atom (L ++ (tm_fvars sL ++ tm_fvars sR))).
    assert (HXnotL : ~ In X L).
    { intro Hin. apply (fresh_atom_notin (L ++ (tm_fvars sL ++ tm_fvars sR))).
      unfold X. apply in_or_app; left; exact Hin. }
    assert (HXnotLbody : ~ In X (tm_fvars sL)).
    { intro Hin. apply (fresh_atom_notin (L ++ (tm_fvars sL ++ tm_fvars sR))).
      unfold X. apply in_or_app; right. apply in_or_app; left; exact Hin. }
    assert (HXnotRbody : ~ In X (tm_fvars sR)).
    { intro Hin. apply (fresh_atom_notin (L ++ (tm_fvars sL ++ tm_fvars sR))).
      unfold X. apply in_or_app; right. apply in_or_app; right; exact Hin. }
    assert (Hsrc : locally_closed_tm (tm_abs T1 t2)).
    { eapply has_type_lc. econstructor; eauto. }
    assert (HplugL : locally_closed_tm (plug_left rho sigma (tm_abs T1 t2))).
    { unfold locally_closed_tm in *. eapply plug_left_lc; [exact Hrlc| |exact Hsrc].
      intros y u v Hlook. exact (proj1 (Hslc y u v Hlook)). }
    assert (HplugR : locally_closed_tm (plug_right rho sigma (tm_abs T1 t2))).
    { unfold locally_closed_tm in *. eapply plug_right_lc; [exact Hrlc| |exact Hsrc].
      intros y u v Hlook. exact (proj2 (Hslc y u v Hlook)). }
    set (fL := plug_left rho sigma (tm_abs T1 t2)).
    set (fR := plug_right rho sigma (tm_abs T1 t2)).
    exists fL,fR. split; [subst fL; constructor|].
    split; [subst fR; constructor|].
    split; [apply v_abs; exact HplugL|].
    split; [apply v_abs; exact HplugR|].
    simpl. split; [apply v_abs; exact HplugL|].
    split; [apply v_abs; exact HplugR|].
    intros a b Hva Hvb Hab.
    set (sigma' := (X, (a,b)) :: sigma).
    assert (Htr' : term_env_related rho (update Gamma X T1) sigma').
    { unfold sigma'. eapply term_env_related_extend; [exact Htr|exact Hva|exact Hvb|exact Hab]. }
    assert (Hslc' : term_env_lc sigma').
    { unfold sigma'. eapply term_env_lc_extend; eauto using value_lc. }
    destruct (H1 X HXnotL rho sigma' Hrwf Hrlc Htr' Hslc')
      as [wL [wR [HrL [HrR [HwL [HwR Hrel]]]]]].
    assert (HbodySubL : plug_left rho sigma' t2 = plug_left rho sigma t2).
    { unfold plug_left. change (subst_term_left ((X,(a,b))::sigma) (subst_tm_ty_rel_left rho t2) =
        subst_term_left sigma (subst_tm_ty_rel_left rho t2)).
      apply subst_term_left_cons_unused. exact HXnotLbody. }
    assert (HargSubL : plug_left rho sigma' (tm_fvar X) = a).
    { unfold plug_left. simpl. unfold lookup_term_subst. simpl. rewrite Nat.eqb_refl. reflexivity. }
    assert (HbodyL : plug_left rho sigma' (open_tm t2 (tm_fvar X)) = open_tm (plug_left rho sigma t2) a).
    { unfold open_tm. rewrite (plug_left_open_rec rho sigma' 0 (tm_fvar X) t2).
      - rewrite HbodySubL, HargSubL. reflexivity.
      - intros y u v Hlook. exact (proj1 (Hslc' y u v Hlook)). }
    assert (HbodySubR : plug_right rho sigma' t2 = plug_right rho sigma t2).
    { unfold plug_right. change (subst_term_right ((X,(a,b))::sigma) (subst_tm_ty_rel_right rho t2) =
        subst_term_right sigma (subst_tm_ty_rel_right rho t2)).
      apply subst_term_right_cons_unused. exact HXnotRbody. }
    assert (HargSubR : plug_right rho sigma' (tm_fvar X) = b).
    { unfold plug_right. simpl. unfold lookup_term_subst. simpl. rewrite Nat.eqb_refl. reflexivity. }
    assert (HbodyR : plug_right rho sigma' (open_tm t2 (tm_fvar X)) = open_tm (plug_right rho sigma t2) b).
    { unfold open_tm. rewrite (plug_right_open_rec rho sigma' 0 (tm_fvar X) t2).
      - rewrite HbodySubR, HargSubR. reflexivity.
      - intros y u v Hlook. exact (proj2 (Hslc' y u v Hlook)). }
    rewrite HbodyL in HrL. rewrite HbodyR in HrR.
    exists wL,wR. split.
    + eapply multi_trans.
      * apply multi_one. eapply ST_AppAbs; eauto.
      * exact HrL.
    + split.
      * eapply multi_trans.
        -- apply multi_one. eapply ST_AppAbs; eauto.
        -- exact HrR.
      * repeat split; assumption.
  - destruct (IHHty1 rho sigma Hrwf Hrlc Htr Hslc)
      as [fL [fR [HfL [HfR [HvfL [HvfR HrelF]]]]]].
    destruct (IHHty2 rho sigma Hrwf Hrlc Htr Hslc)
      as [aL [aR [HaL [HaR [HvaL [HvaR HrelA]]]]]].
    simpl in HrelF. destruct HrelF as [_ [_ Happly]].
    destruct (Happly aL aR HvaL HvaR HrelA)
      as [wL [wR [HwL [HwR [HvwL [HvwR Hrel]]]]]].
    exists wL,wR. split.
    + eapply multi_trans.
      * eapply multi_trans.
        -- apply multi_app_left; [exact HfL|].
           { eapply plug_left_lc; [exact Hrlc| |].
             - intros x a b Hlook. exact (proj1 (Hslc x a b Hlook)).
             - eapply has_type_lc; exact Hty2. }
        -- apply multi_app_right; [exact HvfL|exact HaL].
      * exact HwL.
    + split.
      * eapply multi_trans.
        -- eapply multi_trans.
           ++ apply multi_app_left; [exact HfR|].
              { eapply plug_right_lc; [exact Hrlc| |].
                - intros x a b Hlook. exact (proj2 (Hslc x a b Hlook)).
                - eapply has_type_lc; exact Hty2. }
           ++ apply multi_app_right; [exact HvfR|exact HaR].
        -- exact HwR.
      * repeat split; assumption.
  - set (pool := L ++ (Delta ++ (context_ty_fvars Gamma ++
      (ty_fvars T ++ (tm_ty_fvars t ++ rel_env_atoms rho)) ))).
    set (X := fresh_atom pool).
    assert (HXnotL : ~ In X L).
    { intro Hin. apply (fresh_atom_notin pool). unfold X,pool. apply in_or_app; left; exact Hin. }
    assert (HXnotDelta : ~ In X Delta).
    { intro Hin. apply (fresh_atom_notin pool). unfold X,pool. apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (HXnotCtx : ~ In X (context_ty_fvars Gamma)).
    { intro Hin. apply (fresh_atom_notin pool). unfold X,pool. apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact Hin. }
    assert (HXnotTy : ~ In X (ty_fvars T)).
    { intro Hin. apply (fresh_atom_notin pool). unfold X,pool.
      apply in_or_app; right. apply in_or_app; right. apply in_or_app; right.
      apply in_or_app; left; exact Hin. }
    assert (HXnotTermTy : ~ In X (tm_ty_fvars t)).
    { intro Hin. apply (fresh_atom_notin pool). unfold X,pool.
      apply in_or_app; right. apply in_or_app; right. apply in_or_app; right.
      apply in_or_app; right. apply in_or_app; left; exact Hin. }
    assert (HXnotRho : ~ In X (rel_env_atoms rho)).
    { intro Hin. apply (fresh_atom_notin pool). unfold X,pool.
      apply in_or_app; right. apply in_or_app; right. apply in_or_app; right.
      apply in_or_app; right. apply in_or_app; right; exact Hin. }
    assert (Hnone : lookup_rel_env X rho = None).
    { eapply lookup_rel_env_none_of_atoms; exact HXnotRho. }
    assert (Hctxfresh : forall x S, lookup_context x Gamma = Some S -> ~ In X (ty_fvars S)).
    { intros x S Hlookup Hin. apply HXnotCtx. eapply lookup_context_ty_fvars; eassumption. }
    assert (Hsrc : locally_closed_tm (tm_tabs t)).
    { eapply has_type_lc. econstructor; eauto. }
    assert (HplugL : locally_closed_tm (plug_left rho sigma (tm_tabs t))).
    { unfold locally_closed_tm in *. eapply plug_left_lc; [exact Hrlc| |exact Hsrc].
      intros x a b Hlook. exact (proj1 (Hslc x a b Hlook)). }
    assert (HplugR : locally_closed_tm (plug_right rho sigma (tm_tabs t))).
    { unfold locally_closed_tm in *. eapply plug_right_lc; [exact Hrlc| |exact Hsrc].
      intros x a b Hlook. exact (proj2 (Hslc x a b Hlook)). }
    set (bodyL := plug_left rho sigma t).
    set (bodyR := plug_right rho sigma t).
    exists (tm_tabs bodyL),(tm_tabs bodyR).
    split; [unfold plug_left; simpl; constructor|].
    split; [unfold plug_right; simpl; constructor|].
    split; [apply v_tabs; exact HplugL|].
    split; [apply v_tabs; exact HplugR|].
    simpl. exists bodyL,bodyR. repeat split; try reflexivity.
    + apply v_tabs; exact HplugL.
    + apply v_tabs; exact HplugR.
    +
    intros U V R HU HV wL wR HmL HmR HwL HwR.
    set (entry := {| rel_env_name := X; rel_env_left_ty := U;
      rel_env_right_ty := V; rel_env_rel := R |}).
    assert (Hname : rel_env_name entry = X) by reflexivity.
    assert (Hrwf' : rel_env_wf (X :: Delta) (entry :: rho)).
    { eapply rel_env_wf_extend; eauto. }
    assert (Hrlc' : rel_env_lc (entry :: rho)).
    { eapply rel_env_lc_extend; eauto. }
    assert (Htr' : term_env_related (entry :: rho) Gamma sigma).
    { eapply term_env_related_world; eauto. }
    pose proof (H0 X HXnotL (entry :: rho) sigma Hrwf' Hrlc' Htr' Hslc)
      as Hfund.
    destruct Hfund as [uL [uR [HuL [HuR [HvuL [HvuR Hrel]]]]]].
    assert (HbodyL : plug_left (entry :: rho) sigma (open_tm_ty t (Ty_FVar X)) =
      open_tm_ty bodyL U).
    { unfold open_tm_ty, bodyL.
      rewrite (plug_left_type_open_rec rho entry X sigma 0 t Hrlc Hname Hnone Hslc HXnotTermTy).
      reflexivity. }
    assert (HbodyR : plug_right (entry :: rho) sigma (open_tm_ty t (Ty_FVar X)) =
      open_tm_ty bodyR V).
    { unfold open_tm_ty, bodyR.
      rewrite (plug_right_type_open_rec rho entry X sigma 0 t Hrlc Hname Hnone Hslc HXnotTermTy).
      reflexivity. }
    rewrite HbodyL in HuL. rewrite HbodyR in HuR.
    assert (HeqL : wL = uL) by (eapply multi_value_unique; eassumption).
    assert (HeqR : wR = uR) by (eapply multi_value_unique; eassumption).
    subst wL wR.
    apply (proj1 (value_rel_world_open_ty_rec T rho entry X [] [] uL uR)).
    + eapply has_type_ty_lc. apply (H X HXnotL).
    + exact Hname.
    + exact Hnone.
    + exact HXnotTy.
    + exact Hrel.
Qed.






Hint Constructors lc_ty_at lc_tm_at value : core.

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

End SystemFParametricityIfRecursionHardTask.
