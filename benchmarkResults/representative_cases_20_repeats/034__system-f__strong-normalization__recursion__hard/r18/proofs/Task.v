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

(* ============================================================ *)
(* Erased (untyped) calculus used for the logical relation.     *)
(* ============================================================ *)

Inductive ut : Type :=
| u_bvar : nat -> ut
| u_fvar : atom -> ut
| u_abs : ut -> ut
| u_app : ut -> ut -> ut
| u_tabs : ut -> ut
| u_tapp : ut -> ut
| u_zero : ut
| u_succ : ut -> ut
| u_natrec : ut -> ut -> ut -> ut.

Fixpoint erase (t : tm) : ut :=
  match t with
  | tm_bvar i => u_bvar i
  | tm_fvar x => u_fvar x
  | tm_abs T b => u_abs (erase b)
  | tm_app t1 t2 => u_app (erase t1) (erase t2)
  | tm_tabs b => u_tabs (erase b)
  | tm_tapp b T => u_tapp (erase b)
  | tm_zero => u_zero
  | tm_succ b => u_succ (erase b)
  | tm_natrec n b s => u_natrec (erase n) (erase b) (erase s)
  end.

Fixpoint open_ut_rec (k : nat) (u t : ut) : ut :=
  match t with
  | u_bvar i => if Nat.eqb k i then u else u_bvar i
  | u_fvar x => u_fvar x
  | u_abs b => u_abs (open_ut_rec (S k) u b)
  | u_app t1 t2 => u_app (open_ut_rec k u t1) (open_ut_rec k u t2)
  | u_tabs b => u_tabs (open_ut_rec k u b)
  | u_tapp b => u_tapp (open_ut_rec k u b)
  | u_zero => u_zero
  | u_succ b => u_succ (open_ut_rec k u b)
  | u_natrec n b s => u_natrec (open_ut_rec k u n) (open_ut_rec k u b) (open_ut_rec k u s)
  end.

Definition open_ut (t u : ut) : ut := open_ut_rec 0 u t.

Fixpoint subst_ut (gamma : atom -> ut) (t : ut) : ut :=
  match t with
  | u_bvar i => u_bvar i
  | u_fvar x => gamma x
  | u_abs b => u_abs (subst_ut gamma b)
  | u_app t1 t2 => u_app (subst_ut gamma t1) (subst_ut gamma t2)
  | u_tabs b => u_tabs (subst_ut gamma b)
  | u_tapp b => u_tapp (subst_ut gamma b)
  | u_zero => u_zero
  | u_succ b => u_succ (subst_ut gamma b)
  | u_natrec n b s => u_natrec (subst_ut gamma n) (subst_ut gamma b) (subst_ut gamma s)
  end.

Fixpoint free_ut (t : ut) : list atom :=
  match t with
  | u_bvar _ => []
  | u_fvar x => [x]
  | u_abs b => free_ut b
  | u_app t1 t2 => free_ut t1 ++ free_ut t2
  | u_tabs b => free_ut b
  | u_tapp b => free_ut b
  | u_zero => []
  | u_succ b => free_ut b
  | u_natrec n b s => free_ut n ++ free_ut b ++ free_ut s
  end.

Fixpoint lc_ut_at (k : nat) (t : ut) : Prop :=
  match t with
  | u_bvar i => i < k
  | u_fvar _ => True
  | u_abs b => lc_ut_at (S k) b
  | u_app t1 t2 => lc_ut_at k t1 /\ lc_ut_at k t2
  | u_tabs b => lc_ut_at k b
  | u_tapp b => lc_ut_at k b
  | u_zero => True
  | u_succ b => lc_ut_at k b
  | u_natrec n b s => lc_ut_at k n /\ lc_ut_at k b /\ lc_ut_at k s
  end.

Definition lc_ut (t : ut) : Prop := lc_ut_at 0 t.

Inductive numeric_ut : ut -> Prop :=
| num_zero : numeric_ut u_zero
| num_succ : forall n, numeric_ut n -> numeric_ut (u_succ n).

Inductive value_ut : ut -> Prop :=
| value_abs : forall b, value_ut (u_abs b)
| value_tabs : forall b, value_ut (u_tabs b)
| value_num : forall n, numeric_ut n -> value_ut n.

Fixpoint numeral_ut (n : nat) : ut :=
  match n with O => u_zero | S m => u_succ (numeral_ut m) end.

Fixpoint is_nat (t : ut) : bool :=
  match t with
  | u_zero => true
  | u_succ n => is_nat n
  | _ => false
  end.

Definition is_val (t : ut) : bool :=
  match t with
  | u_abs _ => true
  | u_tabs _ => true
  | _ => is_nat t
  end.

Fixpoint ustep (t : ut) : option ut :=
  match t with
  | u_bvar _ => None
  | u_fvar _ => None
  | u_abs _ => None
  | u_tabs _ => None
  | u_zero => None
  | u_succ b =>
      match ustep b with Some b' => Some (u_succ b') | None => None end
  | u_tapp b =>
      match ustep b with
      | Some b' => Some (u_tapp b')
      | None => match b with u_tabs c => Some c | _ => None end
      end
  | u_app t1 t2 =>
      match ustep t1 with
      | Some t1' => Some (u_app t1' t2)
      | None =>
          match t1 with
          | u_abs b =>
              match is_val t2 with
              | true => Some (open_ut b t2)
              | false =>
                  match ustep t2 with
                  | Some t2' => Some (u_app t1 t2')
                  | None => None
                  end
              end
          | _ =>
              match is_val t1 with
              | true =>
                  match ustep t2 with
                  | Some t2' => Some (u_app t1 t2')
                  | None => None
                  end
              | false => None
              end
          end
      end
  | u_natrec n b s =>
      match ustep n with
      | Some n' => Some (u_natrec n' b s)
      | None =>
          match is_nat n with
          | true =>
              match ustep b with
              | Some b' => Some (u_natrec n b' s)
              | None =>
                  match is_val b with
                  | true =>
                      match ustep s with
                      | Some s' => Some (u_natrec n b s')
                      | None =>
                          match is_val s with
                          | true =>
                              match n with
                              | u_zero => Some b
                              | u_succ n' => Some (u_app (u_app s n') (u_natrec n' b s))
                              | _ => None
                              end
                          | false => None
                          end
                      end
                  | false => None
                  end
              end
          | false => None
          end
      end
  end.

Definition natrec_result (n b s : ut) : ut :=
  match n with
  | u_zero => b
  | u_succ n' => u_app (u_app s n') (u_natrec n' b s)
  | _ => b
  end.

Inductive SN_ut : ut -> Prop :=
| SN_ut_intro : forall t,
    (forall u, ustep t = Some u -> SN_ut u) -> SN_ut t.

(* ---------- basic semantic lemmas for the erased calculus ---------- *)

Lemma is_nat_spec : forall t, is_nat t = true <-> numeric_ut t.
Proof.
  induction t; simpl; try (split; [discriminate | inversion 1]).
  - (* u_zero *) split; [intros _ | intros _]; constructor.
  - (* u_succ *) rewrite IHt. split.
    + intro H; apply num_succ; assumption.
    + intro H; inversion H; subst; assumption.
Qed.

Lemma value_ut_cases : forall t, value_ut t ->
    (exists b, t = u_abs b) \/ (exists b, t = u_tabs b) \/ numeric_ut t.
Proof.
  intros t H. inversion H; subst.
  - left; eauto.
  - right; left; eauto.
  - right; right; assumption.
Qed.

Lemma is_val_spec : forall t, is_val t = true <-> value_ut t.
Proof.
  intros t. destruct t as [i | a | b | t1 t2 | b | b | | b | n b s]; simpl.
  - (* bvar *) split; [discriminate | intro Hv].
    destruct (value_ut_cases (u_bvar i) Hv) as [[c Hc] | [[c Hc] | Hn]]; try discriminate.
    inversion Hn.
  - (* fvar *) split; [discriminate | intro Hv].
    destruct (value_ut_cases (u_fvar a) Hv) as [[c Hc] | [[c Hc] | Hn]]; try discriminate.
    inversion Hn.
  - (* abs *) split; [intros _ | intros _]; constructor.
  - (* app *) split; [discriminate | intro Hv].
    destruct (value_ut_cases (u_app t1 t2) Hv) as [[c Hc] | [[c Hc] | Hn]]; try discriminate.
    inversion Hn.
  - (* tabs *) split; [intros _ | intros _]; constructor.
  - (* tapp *) split; [discriminate | intro Hv].
    destruct (value_ut_cases (u_tapp b) Hv) as [[c Hc] | [[c Hc] | Hn]]; try discriminate.
    inversion Hn.
  - (* zero *) split.
    + intros _. apply value_num. constructor.
    + intros _. reflexivity.
  - (* succ *) split.
    + intro H. apply value_num. constructor.
      apply (proj1 (is_nat_spec b)). exact H.
    + intro Hv.
      destruct (value_ut_cases (u_succ b) Hv) as [[c Hc] | [[c Hc] | Hn]]; try discriminate.
      inversion Hn; subst.
      apply (proj2 (is_nat_spec b)). assumption.
  - (* natrec *) split; [discriminate | intro Hv].
    destruct (value_ut_cases (u_natrec n b s) Hv) as [[c Hc] | [[c Hc] | Hn]]; try discriminate.
    inversion Hn.
Qed.

Lemma is_val_false : forall t, ~ value_ut t -> is_val t = false.
Proof.
  intros t H. destruct (is_val t) eqn:E; auto.
  exfalso. apply H. apply (proj1 (is_val_spec t)). exact E.
Qed.

Lemma numeric_ut_value : forall t, numeric_ut t -> value_ut t.
Proof. intros; apply value_num; assumption. Qed.

Lemma numeric_ut_lc_at : forall t k, numeric_ut t -> lc_ut_at k t.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma numeric_ut_lc : forall t, numeric_ut t -> lc_ut t.
Proof. intros; apply numeric_ut_lc_at. assumption. Qed.

Lemma numeric_ut_ustep_none : forall t, numeric_ut t -> ustep t = None.
Proof.
  intros t Hn. induction Hn as [| n Hn IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma value_ut_ustep_none : forall t, value_ut t -> ustep t = None.
Proof.
  intros t Hv. induction Hv as [b | b | n Hn].
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. apply numeric_ut_ustep_none. exact Hn.
Qed.

Lemma ustep_not_value : forall t u, ustep t = Some u -> ~ value_ut t.
Proof.
  intros t u H Hv.
  rewrite (value_ut_ustep_none t Hv) in H. discriminate.
Qed.

Lemma SN_ut_no_step : forall t, ustep t = None -> SN_ut t.
Proof.
  intros t H. apply SN_ut_intro. intros u Hu. rewrite H in Hu. discriminate.
Qed.

Lemma SN_ut_fwd : forall t u, SN_ut t -> ustep t = Some u -> SN_ut u.
Proof.
  intros t u H. induction H as [t0 Hreds IH]. intros Hu.
  apply Hreds. exact Hu.
Qed.

Lemma SN_ut_back : forall t u, ustep t = Some u -> SN_ut u -> SN_ut t.
Proof.
  intros t u H Hu. apply SN_ut_intro. intros v Hv.
  rewrite H in Hv. injection Hv as ->. exact Hu.
Qed.

Lemma value_ut_SN : forall t, value_ut t -> SN_ut t.
Proof. intros; apply SN_ut_no_step; apply value_ut_ustep_none; assumption. Qed.

Lemma ustep_abs : forall b, ustep (u_abs b) = None.
Proof. reflexivity. Qed.
Lemma ustep_tabs : forall b, ustep (u_tabs b) = None.
Proof. reflexivity. Qed.
Lemma ustep_zero : ustep u_zero = None.
Proof. reflexivity. Qed.

Lemma ustep_succ_step : forall t u, ustep t = Some u -> ustep (u_succ t) = Some (u_succ u).
Proof. intros t u H. simpl. rewrite H. reflexivity. Qed.

Lemma ustep_succ_none : forall t, ustep t = None -> ustep (u_succ t) = None.
Proof. intros t H. simpl. rewrite H. reflexivity. Qed.

Lemma ustep_app_head_step : forall t u v,
    ustep t = Some u -> ustep (u_app t v) = Some (u_app u v).
Proof. intros t u v H. simpl. rewrite H. reflexivity. Qed.

Lemma ustep_app_abs_value : forall b v,
    value_ut v -> ustep (u_app (u_abs b) v) = Some (open_ut b v).
Proof.
  intros b v Hv. simpl.
  rewrite (proj2 (is_val_spec v) Hv). reflexivity.
Qed.

Lemma ustep_app_abs_step_noval : forall b v v',
    is_val v = false -> ustep v = Some v' ->
    ustep (u_app (u_abs b) v) = Some (u_app (u_abs b) v').
Proof.
  intros b v v' Hv Hs. simpl. rewrite Hv, Hs. reflexivity.
Qed.

Lemma ustep_app_abs_stuck_noval : forall b v,
    is_val v = false -> ustep v = None -> ustep (u_app (u_abs b) v) = None.
Proof.
  intros b v Hv Hs. simpl. rewrite Hv, Hs. reflexivity.
Qed.

Lemma ustep_app_value_step : forall v1 v2 v2',
    value_ut v1 -> ustep v2 = Some v2' ->
    ustep (u_app v1 v2) = Some (u_app v1 v2').
Proof.
  intros v1 v2 v2' Hv Hs.
  destruct Hv as [b | b | n Hn].
  - simpl. rewrite (is_val_false v2 (ustep_not_value v2 v2' Hs)).
    rewrite Hs. reflexivity.
  - simpl. rewrite Hs. reflexivity.
  - destruct Hn as [| m Hm]; simpl.
    + rewrite Hs. reflexivity.
    + rewrite (numeric_ut_ustep_none m Hm).
      rewrite (proj2 (is_nat_spec m) Hm).
      rewrite Hs. reflexivity.
Qed.

Lemma ustep_tapp_step : forall t u, ustep t = Some u -> ustep (u_tapp t) = Some (u_tapp u).
Proof. intros t u H. simpl. rewrite H. reflexivity. Qed.

Lemma ustep_tapp_tabs : forall b, ustep (u_tapp (u_tabs b)) = Some b.
Proof. intros b. simpl. reflexivity. Qed.

Lemma ustep_tapp_stuck : forall t,
    ustep t = None -> ~ value_ut t -> ustep (u_tapp t) = None.
Proof.
  intros t Hns Hnv. destruct t as [i | a | b | t1 t2 | b | b | | b | n b s]; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* app *)
    change (match ustep (u_app t1 t2) with
            | Some b' => Some (u_tapp b')
            | None => match u_app t1 t2 with u_tabs c => Some c | _ => None end
            end = None).
    rewrite Hns. cbn. reflexivity.
  - (* tabs *) exfalso; apply Hnv; constructor.
  - (* tapp *)
    change (match ustep (u_tapp b) with
            | Some b' => Some (u_tapp b')
            | None => match u_tapp b with u_tabs c => Some c | _ => None end
            end = None).
    rewrite Hns. cbn. reflexivity.
  - reflexivity.
  - (* succ *)
    change (match ustep (u_succ b) with
            | Some b' => Some (u_tapp b')
            | None => match u_succ b with u_tabs c => Some c | _ => None end
            end = None).
    rewrite Hns. cbn. reflexivity.
  - (* natrec *)
    change (match ustep (u_natrec n b s) with
            | Some b' => Some (u_tapp b')
            | None => match u_natrec n b s with u_tabs c => Some c | _ => None end
            end = None).
    rewrite Hns. cbn. reflexivity.
Qed.

Lemma ustep_natrec_arg : forall n n' b s,
    ustep n = Some n' -> ustep (u_natrec n b s) = Some (u_natrec n' b s).
Proof. intros. cbn [ustep]. rewrite H. reflexivity. Qed.

Lemma ustep_natrec_base : forall n b b' s,
    ustep n = None -> is_nat n = true -> ustep b = Some b' ->
    ustep (u_natrec n b s) = Some (u_natrec n b' s).
Proof. intros. cbn [ustep]. rewrite H, H0, H1. reflexivity. Qed.

Lemma ustep_natrec_step : forall n b s s',
    ustep n = None -> is_nat n = true -> ustep b = None -> is_val b = true ->
    ustep s = Some s' -> ustep (u_natrec n b s) = Some (u_natrec n b s').
Proof. intros. cbn [ustep]. rewrite H, H0, H1, H2, H3. reflexivity. Qed.

Lemma ustep_natrec_zero : forall b s,
    ustep b = None -> is_val b = true -> ustep s = None -> is_val s = true ->
    ustep (u_natrec u_zero b s) = Some b.
Proof. intros. cbn [ustep]. rewrite H, H0, H1, H2. reflexivity. Qed.

Lemma ustep_natrec_succ : forall n b s,
    ustep n = None -> is_nat n = true -> ustep b = None -> is_val b = true ->
    ustep s = None -> is_val s = true ->
    ustep (u_natrec (u_succ n) b s) = Some (u_app (u_app s n) (u_natrec n b s)).
Proof. intros. cbn [ustep]. cbn [is_nat].
  rewrite H, H0, H1, H2, H3, H4. reflexivity. Qed.

Lemma ustep_natrec_not_nat : forall n b s,
    ustep n = None -> is_nat n = false -> ustep (u_natrec n b s) = None.
Proof. intros. cbn [ustep]. rewrite H, H0. reflexivity. Qed.

Lemma ustep_natrec_stuck_b : forall n b s,
    ustep n = None -> is_nat n = true -> ustep b = None -> is_val b = false ->
    ustep (u_natrec n b s) = None.
Proof. intros. cbn [ustep]. rewrite H, H0, H1, H2. reflexivity. Qed.

Lemma ustep_natrec_stuck_s : forall n b s,
    ustep n = None -> is_nat n = true -> ustep b = None -> is_val b = true ->
    ustep s = None -> is_val s = false -> ustep (u_natrec n b s) = None.
Proof. intros. cbn [ustep]. rewrite H, H0, H1, H2, H3, H4. reflexivity. Qed.

Lemma ustep_natrec_values : forall n b s,
    numeric_ut n -> value_ut b -> value_ut s ->
    ustep (u_natrec n b s) = Some (natrec_result n b s).
Proof.
  intros n b s Hn Hb Hs.
  pose proof (numeric_ut_ustep_none n Hn) as Hns.
  pose proof (value_ut_ustep_none b Hb) as Hnb.
  pose proof (value_ut_ustep_none s Hs) as Hns2.
  pose proof (proj2 (is_nat_spec n) Hn) as Hin.
  pose proof (proj2 (is_val_spec b) Hb) as Hib.
  pose proof (proj2 (is_val_spec s) Hs) as His.
  destruct Hn as [| n' Hn'].
  - apply ustep_natrec_zero; assumption.
  - apply ustep_natrec_succ.
    + apply numeric_ut_ustep_none; assumption.
    + apply (proj2 (is_nat_spec n')); assumption.
    + exact Hnb.
    + exact Hib.
    + exact Hns2.
    + exact His.
Qed.

Lemma lc_ut_at_mono : forall t k k', lc_ut_at k t -> k <= k' -> lc_ut_at k' t.
Proof.
  induction t; simpl; intros k k' H Hle; auto; try lia.
  - (* u_abs *) apply IHt with (k := S k); [exact H | lia].
  - (* u_app *) destruct H as [H1 H2]. split.
    + apply IHt1 with (k := k); assumption.
    + apply IHt2 with (k := k); assumption.
  - (* u_tabs *) apply IHt with (k := k); assumption.
  - (* u_tapp *) apply IHt with (k := k); assumption.
  - (* u_succ *) apply IHt with (k := k); assumption.
  - (* u_natrec *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply IHt1 with (k := k); assumption.
    + apply IHt2 with (k := k); assumption.
    + apply IHt3 with (k := k); assumption.
Qed.

Lemma lc_ut_at_open_id : forall t m, lc_ut_at m t ->
    forall k u, m <= k -> open_ut_rec k u t = t.
Proof.
  induction t; simpl; intros m Hm k u Hle.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst. simpl in Hm. lia.
    + reflexivity.
  - (* fvar *) reflexivity.
  - (* abs *) rewrite (IHt (S m) Hm (S k) u); [reflexivity | lia].
  - (* app *) destruct Hm as [H1 H2].
    rewrite (IHt1 m H1 k u Hle), (IHt2 m H2 k u Hle). reflexivity.
  - (* tabs *) rewrite (IHt m Hm k u Hle). reflexivity.
  - (* tapp *) rewrite (IHt m Hm k u Hle). reflexivity.
  - (* zero *) reflexivity.
  - (* succ *) rewrite (IHt m Hm k u Hle). reflexivity.
  - (* natrec *) destruct Hm as [H1 [H2 H3]].
    rewrite (IHt1 m H1 k u Hle), (IHt2 m H2 k u Hle), (IHt3 m H3 k u Hle).
    reflexivity.
Qed.

Lemma lc_ut_open_inv : forall t m k x,
    lc_ut_at m (open_ut_rec k (u_fvar x) t) -> lc_ut_at (Nat.max m (S k)) t.
Proof.
  induction t; intros m k x H; simpl in *.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst k.
      apply Nat.lt_le_trans with (S n); [lia | apply Nat.le_max_r].
    + apply Nat.eqb_neq in E.
      apply Nat.lt_le_trans with m; [exact H | apply Nat.le_max_l].
  - (* fvar *) exact I.
  - (* abs *) rewrite Nat.succ_max_distr.
    apply IHt with (m := S m) (k := S k) (x := x). exact H.
  - (* app *) destruct H as [H1 H2]. split.
    + apply IHt1 with (m := m) (k := k) (x := x); exact H1.
    + apply IHt2 with (m := m) (k := k) (x := x); exact H2.
  - (* tabs *) apply IHt with (m := m) (k := k) (x := x); exact H.
  - (* tapp *) apply IHt with (m := m) (k := k) (x := x); exact H.
  - (* zero *) exact I.
  - (* succ *) apply IHt with (m := m) (k := k) (x := x); exact H.
  - (* natrec *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply IHt1 with (m := m) (k := k) (x := x); exact H1.
    + apply IHt2 with (m := m) (k := k) (x := x); exact H2.
    + apply IHt3 with (m := m) (k := k) (x := x); exact H3.
Qed.

Lemma lc_ty_at_mono : forall T k k', lc_ty_at k T -> k <= k' -> lc_ty_at k' T.
Proof.
  induction T; intros k k' H Hle.
  - (* bvar *) inversion H; subst. constructor. lia.
  - (* fvar *) constructor.
  - (* arrow *) inversion H; subst. constructor.
    + apply IHT1 with (k := k); assumption.
    + apply IHT2 with (k := k); assumption.
  - (* all *) apply lc_ty_all. apply IHT with (k := S k).
    + inversion H; subst; assumption.
    + lia.
  - (* nat *) constructor.
Qed.

Lemma lc_ty_at_all_inv : forall k T, lc_ty_at k (Ty_All T) -> lc_ty_at (S k) T.
Proof. intros k T H. inversion H. subst. assumption. Qed.

Lemma lc_ty_at_arrow_inv_1 : forall k T1 T2, lc_ty_at k (Ty_Arrow T1 T2) -> lc_ty_at k T1.
Proof. intros k T1 T2 H. inversion H. subst. assumption. Qed.

Lemma lc_ty_at_arrow_inv_2 : forall k T1 T2, lc_ty_at k (Ty_Arrow T1 T2) -> lc_ty_at k T2.
Proof. intros k T1 T2 H. inversion H. subst. assumption. Qed.

Lemma lc_ty_open_inv : forall T m k X,
    lc_ty_at m (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (Nat.max m (S k)) T.
Proof.
  induction T; intros m k X H; simpl in *.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst k. constructor.
      apply Nat.lt_le_trans with (S n); [lia | apply Nat.le_max_r].
    + apply Nat.eqb_neq in E. inversion H; subst. constructor.
      apply Nat.lt_le_trans with m; [assumption | apply Nat.le_max_l].
  - (* fvar *) constructor.
  - (* arrow *) inversion H; subst. constructor.
    + apply IHT1 with (m := m) (k := k) (X := X); assumption.
    + apply IHT2 with (m := m) (k := k) (X := X); assumption.
  - (* all *) apply lc_ty_all. rewrite Nat.succ_max_distr.
    apply IHT with (m := S m) (k := S k) (X := X).
    inversion H; subst; assumption.
  - (* nat *) constructor.
Qed.

Lemma lc_ty_open_fwd : forall T k U,
    lc_ty_at (S k) T -> lc_ty_at 0 U -> lc_ty_at k (open_ty_rec k U T).
Proof.
  induction T; intros k U HT HU; simpl in *.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst.
      apply lc_ty_at_mono with (k := 0); [assumption | lia].
    + apply Nat.eqb_neq in E. inversion HT; subst. constructor. lia.
  - (* fvar *) constructor.
  - (* arrow *) inversion HT; subst. constructor.
    + apply IHT1 with (k := k); assumption.
    + apply IHT2 with (k := k); assumption.
  - (* all *) apply lc_ty_all. apply IHT with (k := S k); [|assumption].
    apply lc_ty_at_all_inv in HT. exact HT.
  - (* nat *) constructor.
Qed.


(* ---------- erasure commutes with opening and substitution ---------- *)

Lemma erase_open_tm_rec : forall k u t,
    erase (open_tm_rec k u t) = open_ut_rec k (erase u) (erase t).
Proof.
  intros k u t. revert k u. induction t; intros k u; simpl.
  - (* tm_bvar *) destruct (Nat.eqb k n); reflexivity.
  - (* tm_fvar *) reflexivity.
  - (* tm_abs *) rewrite IHt. reflexivity.
  - (* tm_app *) rewrite IHt1, IHt2. reflexivity.
  - (* tm_tabs *) rewrite IHt. reflexivity.
  - (* tm_tapp *) rewrite IHt. reflexivity.
  - (* tm_zero *) reflexivity.
  - (* tm_succ *) rewrite IHt. reflexivity.
  - (* tm_natrec *) rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma erase_open_tm : forall t u,
    erase (open_tm t u) = open_ut (erase t) (erase u).
Proof. intros. apply erase_open_tm_rec. Qed.

Lemma erase_open_tm_ty_rec : forall k U t,
    erase (open_tm_ty_rec k U t) = erase t.
Proof.
  intros k U t. revert k U. induction t; intros k U; simpl.
  - reflexivity.
  - reflexivity.
  - (* tm_abs *) rewrite IHt. reflexivity.
  - (* tm_app *) rewrite IHt1, IHt2. reflexivity.
  - (* tm_tabs *) rewrite IHt. reflexivity.
  - (* tm_tapp *) rewrite IHt. reflexivity.
  - reflexivity.
  - (* tm_succ *) rewrite IHt. reflexivity.
  - (* tm_natrec *) rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma erase_open_tm_ty : forall t U,
    erase (open_tm_ty t U) = erase t.
Proof. intros. apply erase_open_tm_ty_rec. Qed.

Lemma erase_numeric : forall n, numeric_value n -> numeric_ut (erase n).
Proof.
  intros n H. induction H; simpl.
  - constructor.
  - constructor. assumption.
Qed.

Lemma erase_value : forall v, value v -> value_ut (erase v).
Proof.
  intros v H. induction H; simpl.
  - apply value_abs.
  - apply value_tabs.
  - apply value_num. apply erase_numeric. assumption.
Qed.

(* ---------- the annotated step relation simulates to ustep ---------- *)

Lemma step_erase : forall t u, step t u -> ustep (erase t) = Some (erase u).
Proof.
  intros t u H. induction H as
    [ T t v Hlc Hv
    | t1 t1' t2 Hst IHst Hlc
    | v1 t2 t2' Hv Hst IHst
    | t T Hlc HlcT
    | t t' T Hst IHst HlcT
    | t t' Hst IHst
    | n n' b s Hst IHst Hlcb Hlcs
    | n b b' s Hnv Hst IHst Hlcs
    | n b s s' Hnv Hvb Hst IHst
    | b s Hvb Hvs
    | n b s Hnv Hvb Hvs ].
  - (* ST_AppAbs *) cbn [erase]. rewrite erase_open_tm.
    apply ustep_app_abs_value. apply erase_value. exact Hv.
  - (* ST_App1 *) cbn [erase]. apply ustep_app_head_step. exact IHst.
  - (* ST_App2 *) cbn [erase]. apply ustep_app_value_step.
    + apply erase_value. exact Hv.
    + exact IHst.
  - (* ST_TAppTabs *) cbn [erase]. rewrite erase_open_tm_ty.
    apply ustep_tapp_tabs.
  - (* ST_TApp *) cbn [erase]. apply ustep_tapp_step. exact IHst.
  - (* ST_Succ *) cbn [erase]. apply ustep_succ_step. exact IHst.
  - (* ST_RecArg *) cbn [erase]. apply ustep_natrec_arg. exact IHst.
  - (* ST_RecBase *) cbn [erase]. apply ustep_natrec_base.
    + apply numeric_ut_ustep_none. apply erase_numeric. exact Hnv.
    + apply (proj2 (is_nat_spec (erase n))). apply erase_numeric. exact Hnv.
    + exact IHst.
  - (* ST_RecStep *) cbn [erase]. apply ustep_natrec_step.
    + apply numeric_ut_ustep_none. apply erase_numeric. exact Hnv.
    + apply (proj2 (is_nat_spec (erase n))). apply erase_numeric. exact Hnv.
    + apply value_ut_ustep_none. apply erase_value. exact Hvb.
    + apply (proj2 (is_val_spec (erase b))). apply erase_value. exact Hvb.
    + exact IHst.
  - (* ST_RecZero *) cbn [erase]. apply ustep_natrec_zero.
    + apply value_ut_ustep_none. apply erase_value. exact Hvb.
    + apply (proj2 (is_val_spec (erase b))). apply erase_value. exact Hvb.
    + apply value_ut_ustep_none. apply erase_value. exact Hvs.
    + apply (proj2 (is_val_spec (erase s))). apply erase_value. exact Hvs.
  - (* ST_RecSucc *) cbn [erase]. apply ustep_natrec_succ.
    + apply numeric_ut_ustep_none. apply erase_numeric. exact Hnv.
    + apply (proj2 (is_nat_spec (erase n))). apply erase_numeric. exact Hnv.
    + apply value_ut_ustep_none. apply erase_value. exact Hvb.
    + apply (proj2 (is_val_spec (erase b))). apply erase_value. exact Hvb.
    + apply value_ut_ustep_none. apply erase_value. exact Hvs.
    + apply (proj2 (is_val_spec (erase s))). apply erase_value. exact Hvs.
Qed.

Lemma SN_annot_of_SN_ut : forall w, SN_ut w ->
    forall t, erase t = w -> strongly_normalizing t.
Proof.
  intros w HSN.
  induction HSN as [w0 Hreds IH].
  intros t Heq. apply SN_intro. intros u Hstep.
  assert (Hustep : ustep (erase t) = Some (erase u)) by (apply step_erase; exact Hstep).
  rewrite Heq in Hustep.
  apply (IH (erase u) Hustep u eq_refl).
Qed.


(* ---------- generic equations for ustep ---------- *)

Lemma ustep_app_generic : forall t1 t2,
  ustep (u_app t1 t2) =
  match ustep t1 with
  | Some t1' => Some (u_app t1' t2)
  | None =>
      match t1 with
      | u_abs b =>
          match is_val t2 with
          | true => Some (open_ut b t2)
          | false => match ustep t2 with Some t2' => Some (u_app t1 t2') | None => None end
          end
      | _ =>
          match is_val t1 with
          | true => match ustep t2 with Some t2' => Some (u_app t1 t2') | None => None end
          | false => None
          end
      end
  end.
Proof. intros; reflexivity. Qed.

Lemma ustep_tapp_generic : forall b,
  ustep (u_tapp b) =
  match ustep b with
  | Some b' => Some (u_tapp b')
  | None => match b with u_tabs c => Some c | _ => None end
  end.
Proof. intros; reflexivity. Qed.

Lemma ustep_succ_generic : forall b,
  ustep (u_succ b) =
  match ustep b with Some b' => Some (u_succ b') | None => None end.
Proof. intros; reflexivity. Qed.

Lemma ustep_natrec_generic : forall n b s,
  ustep (u_natrec n b s) =
  match ustep n with
  | Some n' => Some (u_natrec n' b s)
  | None =>
      match is_nat n with
      | true =>
          match ustep b with
          | Some b' => Some (u_natrec n b' s)
          | None =>
              match is_val b with
              | true =>
                  match ustep s with
                  | Some s' => Some (u_natrec n b s')
                  | None =>
                      match is_val s with
                      | true =>
                          match n with
                          | u_zero => Some b
                          | u_succ n' => Some (u_app (u_app s n') (u_natrec n' b s))
                          | _ => None
                          end
                      | false => None
                      end
                  end
              | false => None
              end
          end
      | false => None
      end
  end.
Proof. intros; reflexivity. Qed.

Lemma ustep_app_neutral : forall t1 t2,
  ustep t1 = None -> is_val t1 = false -> ustep (u_app t1 t2) = None.
Proof.
  intros t1 t2 H1 Hv. rewrite ustep_app_generic. rewrite H1.
  destruct t1; simpl in *.
  - reflexivity.
  - reflexivity.
  - discriminate Hv.
  - reflexivity.
  - discriminate Hv.
  - reflexivity.
  - discriminate Hv.
  - rewrite Hv. reflexivity.
  - reflexivity.
Qed.

Lemma ustep_app_tabs_stuck : forall b t2,
  ustep t2 = None -> ustep (u_app (u_tabs b) t2) = None.
Proof.
  intros b t2 H2. rewrite ustep_app_generic. rewrite ustep_tabs.
  rewrite (proj2 (is_val_spec (u_tabs b)) (value_tabs b)).
  rewrite H2. reflexivity.
Qed.

Lemma ustep_app_numeric_stuck : forall n t2,
  numeric_ut n -> ustep t2 = None -> ustep (u_app n t2) = None.
Proof.
  intros n t2 Hn H2. destruct Hn as [| m Hm].
  - rewrite ustep_app_generic. rewrite ustep_zero.
    rewrite (proj2 (is_val_spec u_zero) (value_num u_zero num_zero)).
    rewrite H2. reflexivity.
  - rewrite ustep_app_generic.
    rewrite (numeric_ut_ustep_none (u_succ m) (num_succ m Hm)).
    rewrite (proj2 (is_val_spec (u_succ m)) (value_num (u_succ m) (num_succ m Hm))).
    rewrite H2. reflexivity.
Qed.

Lemma ustep_app_value_stuck : forall t1 t2,
  value_ut t1 -> (forall b, t1 <> u_abs b) -> ustep t2 = None ->
  ustep (u_app t1 t2) = None.
Proof.
  intros t1 t2 Hv Hnab H2.
  destruct Hv as [b | b | n Hn].
  - exfalso. apply (Hnab b). reflexivity.
  - apply ustep_app_tabs_stuck. exact H2.
  - apply ustep_app_numeric_stuck; assumption.
Qed.

(* ---------- lc is preserved by opening and by a step ---------- *)

Lemma lc_ut_open_gen : forall t d,
    lc_ut_at (S d) t ->
    forall u, lc_ut u -> lc_ut_at d (open_ut_rec d u t).
Proof.
  induction t; intros d Ht u Hu; simpl in *.
  - (* bvar *) destruct (Nat.eqb d n) eqn:E.
    + apply Nat.eqb_eq in E. subst d.
      apply lc_ut_at_mono with (k := 0); [exact Hu | lia].
    + apply Nat.eqb_neq in E. simpl. lia.
  - (* fvar *) exact I.
  - (* abs *) apply IHt with (d := S d); [simpl in Ht; exact Ht | exact Hu].
  - (* app *) destruct Ht as [H1 H2]. split.
    + apply IHt1 with (d := d); [exact H1 | exact Hu].
    + apply IHt2 with (d := d); [exact H2 | exact Hu].
  - (* tabs *) apply IHt with (d := d); [exact Ht | exact Hu].
  - (* tapp *) apply IHt with (d := d); [exact Ht | exact Hu].
  - (* zero *) exact I.
  - (* succ *) apply IHt with (d := d); [exact Ht | exact Hu].
  - (* natrec *) destruct Ht as [H1 [H2 H3]]. split; [|split].
    + apply IHt1 with (d := d); [exact H1 | exact Hu].
    + apply IHt2 with (d := d); [exact H2 | exact Hu].
    + apply IHt3 with (d := d); [exact H3 | exact Hu].
Qed.


Lemma lc_ut_step_fwd : forall t u, lc_ut t -> ustep t = Some u -> lc_ut u.
Proof.
  intros t. induction t as
    [ i | a | b IHabs | t1 IH1 t2 IH2 | b IHtabs | b IHtapp | | b IHsucc | n IHn b IHb s IHs ];
    intros u Hlc Hstep.
  - (* bvar *) simpl in *. discriminate Hstep.
  - (* fvar *) simpl in *. discriminate Hstep.
  - (* abs *) simpl in *. discriminate Hstep.
  - (* app *)
    rewrite ustep_app_generic in Hstep.
    simpl in Hlc. destruct Hlc as [Hlc1 Hlc2].
    destruct (ustep t1) as [t1'|] eqn:E1.
    + simpl in Hstep. injection Hstep as <-. simpl. split.
      * apply (IH1 t1' Hlc1). reflexivity.
      * exact Hlc2.
    + destruct (is_val t1) eqn:E1v.
      * (* t1 is a value *) destruct t1 as [i|a|b|s1 s2|b|b| |b|nn bb ss].
        -- (* bvar *) simpl in E1v. discriminate E1v.
        -- (* fvar *) simpl in E1v. discriminate E1v.
        -- (* abs b *)
           change (ustep (u_app (u_abs b) t2) = Some u) in Hstep.
           destruct (is_val t2) eqn:E2v.
           ++ apply is_val_spec in E2v.
              rewrite (ustep_app_abs_value b t2 E2v) in Hstep.
              injection Hstep as <-.
              apply lc_ut_open_gen with (d := 0).
              ** simpl in Hlc1. exact Hlc1.
              ** exact Hlc2.
           ++ destruct (ustep t2) as [t2'|] eqn:E2.
              --- rewrite (ustep_app_abs_step_noval b t2 t2' E2v E2) in Hstep.
                  injection Hstep as <-. simpl. split.
                  +++ simpl in Hlc1. exact Hlc1.
                  +++ apply (IH2 t2' Hlc2). reflexivity.
              --- rewrite (ustep_app_abs_stuck_noval b t2 E2v E2) in Hstep.
                  discriminate Hstep.
        -- (* app *) simpl in E1v. discriminate E1v.
        -- (* tabs b *)
           change (ustep (u_app (u_tabs b) t2) = Some u) in Hstep.
           destruct (ustep t2) as [t2'|] eqn:E2.
           ++ rewrite (ustep_app_value_step (u_tabs b) t2 t2' (value_tabs b) E2) in Hstep.
              injection Hstep as <-. simpl. split.
              ** exact Hlc1.
              ** apply (IH2 t2' Hlc2). reflexivity.
           ++ rewrite (ustep_app_tabs_stuck b t2 E2) in Hstep. discriminate Hstep.
        -- (* tapp *) simpl in E1v. discriminate E1v.
        -- (* zero *)
           change (ustep (u_app u_zero t2) = Some u) in Hstep.
           destruct (ustep t2) as [t2'|] eqn:E2.
           ++ rewrite (ustep_app_value_step u_zero t2 t2' (value_num u_zero num_zero) E2) in Hstep.
              injection Hstep as <-. simpl. split.
              ** exact Hlc1.
              ** apply (IH2 t2' Hlc2). reflexivity.
           ++ rewrite (ustep_app_numeric_stuck u_zero t2 num_zero E2) in Hstep. discriminate Hstep.
        -- (* succ b *)
           simpl in Hstep. simpl in E1v.
           assert (Hn : numeric_ut b) by (apply (proj1 (is_nat_spec b)); exact E1v).
           destruct (ustep t2) as [t2'|] eqn:E2.
           ++ simpl in Hstep. injection Hstep as <-. simpl. split.
              ** simpl in Hlc1. exact Hlc1.
              ** apply (IH2 t2' Hlc2). reflexivity.
           ++ discriminate Hstep.
        -- (* natrec *) simpl in E1v. discriminate E1v.
      * (* t1 is not a value *) destruct t1 as [i|a|b|s1 s2|b|b| |b|nn bb ss].
        -- (* bvar *) simpl in Hstep. discriminate Hstep.
        -- (* fvar *) simpl in Hstep. discriminate Hstep.
        -- (* abs *) simpl in E1v. discriminate E1v.
        -- (* app *) simpl in Hstep. discriminate Hstep.
        -- (* tabs *) simpl in E1v. discriminate E1v.
        -- (* tapp *) simpl in Hstep. discriminate Hstep.
        -- (* zero *) simpl in E1v. discriminate E1v.
        -- (* succ b *) simpl in Hstep. simpl in E1v. discriminate Hstep.
        -- (* natrec *) simpl in Hstep. discriminate Hstep.
  - (* tabs *) simpl in *. discriminate Hstep.
  - (* tapp *)
    rewrite ustep_tapp_generic in Hstep.
    simpl in Hlc.
    destruct (ustep b) as [b'|] eqn:E1.
    + simpl in Hstep. injection Hstep as <-. simpl.
      apply (IHtapp b' Hlc). reflexivity.
    + destruct b as [i|a|c|s1 s2|c|c| |c|nn bb ss].
      * simpl in Hstep. discriminate Hstep.
      * simpl in Hstep. discriminate Hstep.
      * simpl in Hstep. discriminate Hstep.
      * simpl in Hstep. discriminate Hstep.
      * simpl in Hstep. injection Hstep as <-. simpl in Hlc. exact Hlc.
      * simpl in Hstep. discriminate Hstep.
      * simpl in Hstep. discriminate Hstep.
      * simpl in Hstep. discriminate Hstep.
      * simpl in Hstep. discriminate Hstep.
  - (* zero *) simpl in *. discriminate Hstep.
  - (* succ *)
    rewrite ustep_succ_generic in Hstep.
    simpl in Hlc.
    destruct (ustep b) as [b'|] eqn:E1.
    + simpl in Hstep. injection Hstep as <-. simpl.
      apply (IHsucc b' Hlc). reflexivity.
    + discriminate Hstep.
  - (* natrec *)
    rewrite ustep_natrec_generic in Hstep.
    simpl in Hlc. destruct Hlc as [Hln [Hlb Hls]].
    destruct (ustep n) as [n'|] eqn:En.
    + simpl in Hstep. injection Hstep as <-. simpl. split; [|split].
      * apply (IHn n' Hln). reflexivity.
      * exact Hlb.
      * exact Hls.
    + destruct (is_nat n) eqn:Inat.
      * destruct (ustep b) as [b'|] eqn:Eb.
        -- simpl in Hstep. injection Hstep as <-. simpl. split; [|split].
           ++ exact Hln.
           ++ apply (IHb b' Hlb). reflexivity.
           ++ exact Hls.
        -- destruct (is_val b) eqn:Ib.
           ++ destruct (ustep s) as [s'|] eqn:Es.
              ** simpl in Hstep. injection Hstep as <-. simpl. split; [|split].
                 --- exact Hln.
                 --- exact Hlb.
                 --- apply (IHs s' Hls). reflexivity.
              ** destruct (is_val s) eqn:Is.
                 --- destruct n as [i|a|bb|s1 s2|bb|bb| |bb|nn bb ss].
                     +++ (* bvar *) simpl in Inat. discriminate Inat.
                     +++ (* fvar *) simpl in Inat. discriminate Inat.
                     +++ (* abs *) simpl in Inat. discriminate Inat.
                     +++ (* app *) simpl in Inat. discriminate Inat.
                     +++ (* tabs *) simpl in Inat. discriminate Inat.
                     +++ (* tapp *) simpl in Inat. discriminate Inat.
                     +++ (* zero *) simpl in Hstep.
                         injection Hstep as <-. exact Hlb.
                     +++ (* succ *)
                         simpl in Hstep.
                         injection Hstep as <-. simpl. split.
                         *** split; [exact Hls | simpl in Hln; exact Hln].
                         *** split; [|split].
                             ---- simpl in Hln; exact Hln.
                             ---- exact Hlb.
                             ---- exact Hls.
                     +++ (* natrec *) simpl in Inat. discriminate Inat.
                 --- simpl in Hstep. discriminate Hstep.
           ++ simpl in Hstep. discriminate Hstep.
      * simpl in Hstep. discriminate Hstep.
Qed.


(* ---------- reducibility candidates ---------- *)

Record cand : Type := {
  car : ut -> Prop;
  cand_sn : forall t, car t -> SN_ut t;
  cand_lc : forall t, car t -> lc_ut t;
  cand_back : forall t u, lc_ut t -> ustep t = Some u -> car u -> car t;
  cand_fwd : forall t u, car t -> ustep t = Some u -> car u;
  cand_neutral : forall t, lc_ut t -> SN_ut t -> ustep t = None -> ~ value_ut t -> car t
}.

Definition arrow_cand (A B : cand) : cand.
Proof.
  refine {| car t := SN_ut t /\ lc_ut t /\ (forall u, car A u -> car B (u_app t u)) |}.
  - intros t [Hsn [Hlc _]]. exact Hsn.
  - intros t [Hsn [Hlc _]]. exact Hlc.
  - intros t u Hlc Hstep [Hsn' [Hlc' Hbody]].
    split; [|split].
    + apply SN_ut_back with u; assumption.
    + exact Hlc.
    + intros v HA.
      apply (cand_back B (u_app t v) (u_app u v)).
      * simpl. split; [exact Hlc | apply (cand_lc A v HA)].
      * apply ustep_app_head_step. exact Hstep.
      * apply Hbody. exact HA.
  - intros t u [Hsn [Hlc Hbody]] Hstep.
    split; [|split].
    + apply SN_ut_fwd with t; assumption.
    + apply lc_ut_step_fwd with t; assumption.
    + intros v HA.
      apply (cand_fwd B (u_app t v) (u_app u v)).
      * apply Hbody. exact HA.
      * apply ustep_app_head_step. exact Hstep.
  - intros t Hlc Hsn Hns Hnv.
    split; [|split].
    + exact Hsn.
    + exact Hlc.
    + intros v HA.
      apply (cand_neutral B (u_app t v)).
      * simpl. split; [exact Hlc | apply (cand_lc A v HA)].
      * apply SN_ut_no_step. apply ustep_app_neutral.
        { exact Hns. }
        { apply is_val_false. exact Hnv. }
      * apply ustep_app_neutral.
        { exact Hns. }
        { apply is_val_false. exact Hnv. }
      * intro Hv; inversion Hv; subst. inversion H.
Defined.

Definition all_cand (F : cand -> cand) : cand.
Proof.
  refine {| car t := SN_ut t /\ lc_ut t /\ (forall S : cand, car (F S) (u_tapp t)) |}.
  - intros t [Hsn [Hlc _]]. exact Hsn.
  - intros t [Hsn [Hlc _]]. exact Hlc.
  - intros t u Hlc Hstep [Hsn' [Hlc' Hbody]].
    split; [|split].
    + apply SN_ut_back with u; assumption.
    + exact Hlc.
    + intros S.
      apply (cand_back (F S) (u_tapp t) (u_tapp u)).
      * simpl. exact Hlc.
      * apply ustep_tapp_step. exact Hstep.
      * apply Hbody.
  - intros t u [Hsn [Hlc Hbody]] Hstep.
    split; [|split].
    + apply SN_ut_fwd with t; assumption.
    + apply lc_ut_step_fwd with t; assumption.
    + intros S.
      apply (cand_fwd (F S) (u_tapp t) (u_tapp u)).
      * apply Hbody.
      * apply ustep_tapp_step. exact Hstep.
  - intros t Hlc Hsn Hns Hnv.
    split; [|split].
    + exact Hsn.
    + exact Hlc.
    + intros S.
      apply (cand_neutral (F S) (u_tapp t)).
      * simpl. exact Hlc.
      * apply SN_ut_no_step. apply ustep_tapp_stuck.
        { exact Hns. }
        { exact Hnv. }
      * apply ustep_tapp_stuck.
        { exact Hns. }
        { exact Hnv. }
      * intro Hv; inversion Hv; subst. inversion H.
Defined.

Definition nat_cand : cand.
Proof.
  refine {| car t := SN_ut t /\ lc_ut t |}.
  - intros t [Hsn Hlc]. exact Hsn.
  - intros t [Hsn Hlc]. exact Hlc.
  - intros t u Hlc Hstep [Hsn' Hlc'].
    split.
    + apply SN_ut_back with u; assumption.
    + exact Hlc.
  - intros t u [Hsn Hlc] Hstep.
    split.
    + apply SN_ut_fwd with t; assumption.
    + apply lc_ut_step_fwd with t; assumption.
  - intros t Hlc Hsn Hns Hnv. split; assumption.
Defined.

Definition cons_cand (S : cand) (rho : nat -> cand) : nat -> cand :=
  fun n => match n with 0 => S | Datatypes.S k => rho k end.

Definition replace_at (k : nat) (c : cand) (rho : nat -> cand) : nat -> cand :=
  fun n => if Nat.eqb n k then c else rho n.

Fixpoint free_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => free_ty T1 ++ free_ty T2
  | Ty_All T1 => free_ty T1
  | Ty_Nat => []
  end.

Fixpoint R_ty (rho : nat -> cand) (sigma : atom -> cand) (T : ty) {struct T} : cand :=
  match T with
  | Ty_BVar i => rho i
  | Ty_FVar X => sigma X
  | Ty_Arrow T1 T2 => arrow_cand (R_ty rho sigma T1) (R_ty rho sigma T2)
  | Ty_All T1 => all_cand (fun S => R_ty (cons_cand S rho) sigma T1)
  | Ty_Nat => nat_cand
  end.

(* ---------- extensionality of candidates and the environment lemmas ---------- *)

Lemma arrow_cand_rel : forall A1 A2 B1 B2,
    (forall t, car A1 t <-> car A2 t) ->
    (forall t, car B1 t <-> car B2 t) ->
    forall t, car (arrow_cand A1 B1) t <-> car (arrow_cand A2 B2) t.
Proof.
  intros A1 A2 B1 B2 HA HB t.
  unfold arrow_cand. simpl.
  split.
  - intros [Hsn [Hlc Hbody]]. split; [|split]; auto.
    intros u Hu. apply (proj1 (HB (u_app t u))). apply Hbody. apply (proj2 (HA u)). exact Hu.
  - intros [Hsn [Hlc Hbody]]. split; [|split]; auto.
    intros u Hu. apply (proj2 (HB (u_app t u))). apply Hbody. apply (proj1 (HA u)). exact Hu.
Qed.

Lemma all_cand_rel : forall F1 F2,
    (forall S t, car (F1 S) t <-> car (F2 S) t) ->
    forall t, car (all_cand F1) t <-> car (all_cand F2) t.
Proof.
  intros F1 F2 HF t.
  unfold all_cand. simpl.
  split.
  - intros [Hsn [Hlc Hbody]]. split; [|split]; auto.
    intros S. apply (proj1 (HF S (u_tapp t))). apply Hbody.
  - intros [Hsn [Hlc Hbody]]. split; [|split]; auto.
    intros S. apply (proj2 (HF S (u_tapp t))). apply Hbody.
Qed.

Lemma R_ty_env_rel : forall T k, lc_ty_at k T ->
    forall rho1 rho2 sigma,
      (forall i, i < k -> forall t, car (rho1 i) t <-> car (rho2 i) t) ->
      forall t, car (R_ty rho1 sigma T) t <-> car (R_ty rho2 sigma T) t.
Proof.
  induction T; intros k Hlc rho1 rho2 sigma Hagree t.
  - (* bvar *) simpl. apply Hagree. inversion Hlc; assumption.
  - (* fvar *) simpl. reflexivity.
  - (* arrow *) simpl.
    apply arrow_cand_rel.
    + apply IHT1 with (k := k).
      * apply lc_ty_at_arrow_inv_1 with (T2 := T2). exact Hlc.
      * exact Hagree.
    + apply IHT2 with (k := k).
      * apply lc_ty_at_arrow_inv_2 with (T1 := T1). exact Hlc.
      * exact Hagree.
  - (* all *) simpl.
    apply all_cand_rel. intros Sc x.
    apply IHT with (k := S k) (rho1 := cons_cand Sc rho1) (rho2 := cons_cand Sc rho2).
    + apply lc_ty_at_all_inv. exact Hlc.
    + intros i Hi. destruct i as [| j].
      * simpl. reflexivity.
      * simpl. apply Hagree. lia.
  - (* nat *) simpl. reflexivity.
Qed.

Lemma R_ty_sigma_rel : forall T rho sigma1 sigma2,
    (forall X, In X (free_ty T) -> sigma1 X = sigma2 X) ->
    forall t, car (R_ty rho sigma1 T) t <-> car (R_ty rho sigma2 T) t.
Proof.
  induction T; intros rho sigma1 sigma2 H t.
  - (* bvar *) simpl. reflexivity.
  - (* fvar *) simpl.
    assert (Heq : sigma1 a = sigma2 a) by (apply H; simpl; auto).
    rewrite Heq. reflexivity.
  - (* arrow *) simpl.
    apply arrow_cand_rel.
    + apply IHT1 with (rho := rho).
      intros X HX. apply H. apply in_or_app. left. exact HX.
    + apply IHT2 with (rho := rho).
      intros X HX. apply H. apply in_or_app. right. exact HX.
  - (* all *) simpl.
    apply all_cand_rel. intros Sc x.
    apply IHT with (rho := cons_cand Sc rho).
    intros X HX. apply H. exact HX.
  - (* nat *) simpl. reflexivity.
Qed.

(* ---------- the semantic type-substitution lemma ---------- *)

Lemma R_ty_open_gen : forall T k U rho sigma,
    lc_ty_at 0 U ->
    lc_ty_at (S k) T ->
    forall t,
      car (R_ty rho sigma (open_ty_rec k U T)) t <->
      car (R_ty (replace_at k (R_ty rho sigma U) rho) sigma T) t.
Proof.
  induction T as [n | a | T1 IHT1 T2 IHT2 | A IHA | ];
    intros k U rho sigma HU HT t; simpl in *.
  - (* bvar *) destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E. subst k. unfold replace_at.
      rewrite Nat.eqb_refl. reflexivity.
    + apply Nat.eqb_neq in E. unfold replace_at.
      assert (Hnk : (n =? k) = false).
      { apply Nat.eqb_neq. intro H. apply E. symmetry. exact H. }
      rewrite Hnk. simpl. reflexivity.
  - (* fvar *) simpl. reflexivity.
  - (* arrow *) simpl.
    apply arrow_cand_rel.
    + apply IHT1 with (k := k) (U := U).
      * exact HU.
      * apply lc_ty_at_arrow_inv_1 with (T2 := T2). exact HT.
    + apply IHT2 with (k := k) (U := U).
      * exact HU.
      * apply lc_ty_at_arrow_inv_2 with (T1 := T1). exact HT.
  - (* all A *) simpl.
    apply all_cand_rel. intros Sc x.
    assert (HTA : lc_ty_at (S (S k)) A) by (apply lc_ty_at_all_inv; exact HT).
    pose proof (IHA (S k) U (cons_cand Sc rho) sigma HU HTA) as HIH.
    set (c := R_ty rho sigma U).
    set (c' := R_ty (cons_cand Sc rho) sigma U).
    set (E1 := replace_at (S k) c' (cons_cand Sc rho)).
    set (E2 := cons_cand Sc (replace_at k c rho)).
    assert (Hagree : forall i, i < S (S k) -> forall z, car (E1 i) z <-> car (E2 i) z).
    { intros i Hi z. destruct i as [| j].
      - simpl. reflexivity.
      - destruct (Nat.eqb j k) eqn:Ej.
        + apply Nat.eqb_eq in Ej. subst j.
          unfold E1, E2, c, c', replace_at, cons_cand. simpl.
          destruct (Nat.eqb k k) eqn:Ekk.
          * simpl. apply (R_ty_env_rel U 0 HU (cons_cand Sc rho) rho sigma).
            intros i' Hi'. lia.
          * apply Nat.eqb_neq in Ekk. exfalso. apply (Ekk eq_refl).
        + unfold E1, E2, c, c', replace_at, cons_cand. simpl.
          rewrite Ej. simpl. reflexivity. }
    split; intro Hx.
    + apply (proj1 (R_ty_env_rel A (S (S k)) HTA E1 E2 sigma Hagree x)).
      apply (proj1 (HIH x)). exact Hx.
    + apply (proj2 (HIH x)).
      apply (proj2 (R_ty_env_rel A (S (S k)) HTA E1 E2 sigma Hagree x)).
      exact Hx.
  - (* nat *) simpl. reflexivity.
Qed.


(* ---------- basic candidate facts and numerals ---------- *)

Lemma fvar_cand : forall X rho sigma T,
    car (R_ty rho sigma T) (u_fvar X).
Proof.
  intros. apply (cand_neutral (R_ty rho sigma T)).
  - simpl. exact I.
  - apply SN_ut_no_step. reflexivity.
  - reflexivity.
  - intro Hv; inversion Hv; subst; inversion H.
Qed.

Lemma numeric_ut_numeral : forall k, numeric_ut (numeral_ut k).
Proof. induction k; simpl; [constructor | constructor; assumption]. Qed.

Lemma SN_ut_numeral : forall k, SN_ut (numeral_ut k).
Proof.
  intro k. apply SN_ut_no_step. apply numeric_ut_ustep_none.
  apply numeric_ut_numeral.
Qed.

Lemma lc_ut_numeral : forall k, lc_ut (numeral_ut k).
Proof.
  intro k. apply numeric_ut_lc. apply numeric_ut_numeral.
Qed.

Lemma nat_cand_numeral : forall k, car nat_cand (numeral_ut k).
Proof. intro k. split; [apply SN_ut_numeral | apply lc_ut_numeral]. Qed.

Lemma numeric_ut_exists : forall t, numeric_ut t -> exists k, t = numeral_ut k.
Proof.
  intros t H. induction H as [| n Hn IH].
  - exists 0. reflexivity.
  - destruct IH as [k Hk]. exists (S k). simpl. rewrite Hk. reflexivity.
Qed.

Lemma SN_ut_succ : forall t, SN_ut t -> SN_ut (u_succ t).
Proof.
  intros t H. induction H as [t0 Hreds IH].
  apply SN_ut_intro. intros v Hv.
  destruct (ustep t0) as [t'|] eqn:E.
  - rewrite (ustep_succ_step t0 t' E) in Hv.
    injection Hv as <-. apply IH. reflexivity.
  - rewrite (ustep_succ_none t0 E) in Hv. discriminate Hv.
Qed.

(* ---------- reducibility of primitive recursion ---------- *)

Lemma natrec_mem_aux : forall C n b s,
    numeric_ut n ->
    SN_ut b -> car C b ->
    SN_ut s -> car (arrow_cand nat_cand (arrow_cand C C)) s ->
    (forall b' s',
        value_ut b' -> value_ut s' -> car C b' ->
        car (arrow_cand nat_cand (arrow_cand C C)) s' ->
        car C (natrec_result n b' s')) ->
    car C (u_natrec n b s).
Proof.
  intros C n b s Hnum Hb Hcb Hs Hds Hterm.
  assert (Hn_none : ustep n = None) by (apply numeric_ut_ustep_none; exact Hnum).
  assert (Hn_true : is_nat n = true) by (apply (proj2 (is_nat_spec n)); exact Hnum).
  revert s Hs Hcb Hds.
  induction Hb as [b0 Hreds_b IHb].
  intros s0 Hs0 Hcb0 Hds0.
  revert Hcb0 Hds0.
  induction Hs0 as [s1 Hreds_s IHs].
  intros Hcb1 Hds1.
  destruct (is_val b0) eqn:Eb.
  - (* b0 is a value *)
    assert (Ebval : value_ut b0) by (apply is_val_spec; exact Eb).
    assert (Hb_none : ustep b0 = None) by (apply value_ut_ustep_none; exact Ebval).
    destruct (ustep s1) as [s'|] eqn:Es.
    + (* s steps *)
      apply (cand_back C (u_natrec n b0 s1) (u_natrec n b0 s')).
      * simpl. split; [|split].
        -- apply numeric_ut_lc. exact Hnum.
        -- apply (cand_lc C b0). exact Hcb1.
        -- apply (cand_lc (arrow_cand nat_cand (arrow_cand C C)) s1). exact Hds1.
      * apply ustep_natrec_step.
        -- exact Hn_none.
        -- exact Hn_true.
        -- exact Hb_none.
        -- exact Eb.
        -- exact Es.
      * apply (IHs s' eq_refl Hcb1).
        apply (cand_fwd (arrow_cand nat_cand (arrow_cand C C)) s1 s' Hds1 Es).
    + (* s does not step *)
      destruct (is_val s1) eqn:Esval.
      * (* s1 is a value: terminal *)
        assert (Esval_val : value_ut s1) by (apply is_val_spec; exact Esval).
        apply (cand_back C (u_natrec n b0 s1) (natrec_result n b0 s1)).
        -- simpl. split; [|split].
           ++ apply numeric_ut_lc. exact Hnum.
           ++ apply (cand_lc C b0). exact Hcb1.
           ++ apply (cand_lc (arrow_cand nat_cand (arrow_cand C C)) s1). exact Hds1.
        -- apply ustep_natrec_values; [exact Hnum | exact Ebval | exact Esval_val].
        -- apply Hterm; [exact Ebval | exact Esval_val | exact Hcb1 | exact Hds1].
      * (* s1 neutral *)
        apply (cand_neutral C (u_natrec n b0 s1)).
        -- simpl. split; [|split].
           ++ apply numeric_ut_lc. exact Hnum.
           ++ apply (cand_lc C b0). exact Hcb1.
           ++ apply (cand_lc (arrow_cand nat_cand (arrow_cand C C)) s1). exact Hds1.
        -- apply SN_ut_no_step. apply ustep_natrec_stuck_s; assumption.
        -- apply ustep_natrec_stuck_s; assumption.
        -- intro Hv; inversion Hv; subst; inversion H.
  - (* b0 is not a value *)
    destruct (ustep b0) as [b'|] eqn:Ebstep.
    + (* b steps *)
      apply (cand_back C (u_natrec n b0 s1) (u_natrec n b' s1)).
      * simpl. split; [|split].
        -- apply numeric_ut_lc. exact Hnum.
        -- apply (cand_lc C b0). exact Hcb1.
        -- apply (cand_lc (arrow_cand nat_cand (arrow_cand C C)) s1). exact Hds1.
      * apply ustep_natrec_base.
        -- exact Hn_none.
        -- exact Hn_true.
        -- exact Ebstep.
      * assert (Hsn_s1 : SN_ut s1) by (apply SN_ut_intro; exact Hreds_s).
        apply (IHb b' eq_refl s1 Hsn_s1).
        -- apply (cand_fwd C b0 b' Hcb1 Ebstep).
        -- exact Hds1.
    + (* b neutral *)
      apply (cand_neutral C (u_natrec n b0 s1)).
      * simpl. split; [|split].
        -- apply numeric_ut_lc. exact Hnum.
        -- apply (cand_lc C b0). exact Hcb1.
        -- apply (cand_lc (arrow_cand nat_cand (arrow_cand C C)) s1). exact Hds1.
      * apply SN_ut_no_step. apply ustep_natrec_stuck_b; assumption.
      * apply ustep_natrec_stuck_b; assumption.
      * intro Hv; inversion Hv; subst; inversion H.
Qed.

Lemma natrec_numeric_mem : forall k C b s,
    car C b ->
    car (arrow_cand nat_cand (arrow_cand C C)) s ->
    car C (u_natrec (numeral_ut k) b s).
Proof.
  induction k as [| k IH]; intros C b s Hcb Hds.
  - apply (natrec_mem_aux C u_zero b s (numeric_ut_numeral 0)
             (cand_sn C b Hcb) Hcb (cand_sn (arrow_cand nat_cand (arrow_cand C C)) s Hds) Hds).
    intros b' s' Hvb Hvs Hcb' Hds'. exact Hcb'.
  - apply (natrec_mem_aux C (u_succ (numeral_ut k)) b s (numeric_ut_numeral (S k))
             (cand_sn C b Hcb) Hcb (cand_sn (arrow_cand nat_cand (arrow_cand C C)) s Hds) Hds).
    intros b' s' Hvb Hvs Hcb' Hds'.
    change (car C (u_app (u_app s' (numeral_ut k)) (u_natrec (numeral_ut k) b' s'))).
    assert (Happ : car (arrow_cand C C) (u_app s' (numeral_ut k))).
    { apply (proj2 (proj2 Hds')). apply nat_cand_numeral. }
    apply (proj2 (proj2 Happ)).
    apply (IH C b' s' Hcb' Hds').
Qed.

Lemma natrec_mem : forall C n b s,
    car nat_cand n ->
    car C b ->
    car (arrow_cand nat_cand (arrow_cand C C)) s ->
    car C (u_natrec n b s).
Proof.
  intros C n b s Hn Hcb Hds.
  destruct Hn as [Hsn Hnlc].
  revert b s Hcb Hds.
  induction Hsn as [n0 Hreds_n IHn].
  intros b s Hcb Hds.
  destruct (is_nat n0) eqn:En.
  - (* numeric *) apply is_nat_spec in En.
    destruct (numeric_ut_exists n0 En) as [k ->].
    apply natrec_numeric_mem; assumption.
  - (* not numeric *)
    destruct (ustep n0) as [n'|] eqn:Enstep.
    + apply (cand_back C (u_natrec n0 b s) (u_natrec n' b s)).
      * simpl. split; [|split].
        -- exact Hnlc.
        -- apply (cand_lc C b). exact Hcb.
        -- apply (cand_lc (arrow_cand nat_cand (arrow_cand C C)) s). exact Hds.
      * apply ustep_natrec_arg. exact Enstep.
      * apply (IHn n' eq_refl (lc_ut_step_fwd n0 n' Hnlc Enstep) b s Hcb Hds).
    + apply (cand_neutral C (u_natrec n0 b s)).
      * simpl. split; [|split].
        -- exact Hnlc.
        -- apply (cand_lc C b). exact Hcb.
        -- apply (cand_lc (arrow_cand nat_cand (arrow_cand C C)) s). exact Hds.
      * apply SN_ut_no_step. apply ustep_natrec_not_nat; assumption.
      * apply ustep_natrec_not_nat; assumption.
      * intro Hv; inversion Hv; subst; inversion H.
Qed.

(* ---------- abstraction application lemma ---------- *)

Lemma abs_app_red : forall eb A B,
    lc_ut (u_abs eb) ->
    (forall u, car A u -> car B (open_ut eb u)) ->
    forall u, SN_ut u -> car A u -> car B (u_app (u_abs eb) u).
Proof.
  intros eb A B Hlc Hbody u Hsn.
  induction Hsn as [u0 Hreds IHu].
  intros HA.
  destruct (is_val u0) eqn:Eval.
  - apply is_val_spec in Eval.
    apply (cand_back B (u_app (u_abs eb) u0) (open_ut eb u0)).
    + simpl. split; [exact Hlc | apply (cand_lc A u0 HA)].
    + apply ustep_app_abs_value. exact Eval.
    + apply Hbody. exact HA.
  - destruct (ustep u0) as [u'|] eqn:Eustep.
    + apply (cand_back B (u_app (u_abs eb) u0) (u_app (u_abs eb) u')).
      * simpl. split; [exact Hlc | apply (cand_lc A u0 HA)].
      * apply ustep_app_abs_step_noval; assumption.
      * apply (IHu u' eq_refl). apply (cand_fwd A u0 u' HA Eustep).
    + apply (cand_neutral B (u_app (u_abs eb) u0)).
      * simpl. split; [exact Hlc | apply (cand_lc A u0 HA)].
      * apply SN_ut_no_step. apply ustep_app_abs_stuck_noval; assumption.
      * apply ustep_app_abs_stuck_noval; assumption.
      * intro Hv; inversion Hv; subst; inversion H.
Qed.


(* ---------- freshness, context and type well-formedness ---------- *)

Fixpoint max_list (l : list atom) : nat :=
  match l with
  | [] => 0
  | x :: xs => Nat.max x (max_list xs)
  end.

Lemma max_list_ge : forall l x, In x l -> x <= max_list l.
Proof.
  induction l as [| y ys IH]; simpl; intros x H.
  - contradiction.
  - destruct H as [-> | H].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (max_list ys); [apply IH; exact H | apply Nat.le_max_r].
Qed.

Definition fresh_atom (l : list atom) : atom := S (max_list l).

Lemma fresh_atom_notin : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l H. unfold fresh_atom in H. apply max_list_ge in H. lia.
Qed.

Lemma notin_app_left : forall (l1 l2 : list atom) x,
    ~ In x (l1 ++ l2) -> ~ In x l1.
Proof. intros l1 l2 x H H1. apply H. apply in_or_app. left. exact H1. Qed.

Lemma notin_app_right : forall (l1 l2 : list atom) x,
    ~ In x (l1 ++ l2) -> ~ In x l2.
Proof. intros l1 l2 x H H1. apply H. apply in_or_app. right. exact H1. Qed.

Fixpoint free_gamma (Gamma : context) : list atom :=
  match Gamma with
  | [] => []
  | (_, T) :: G => free_ty T ++ free_gamma G
  end.

Lemma free_gamma_in : forall Gamma y T,
    lookup_context y Gamma = Some T ->
    forall X, In X (free_ty T) -> In X (free_gamma Gamma).
Proof.
  induction Gamma as [| [z Tz] G IH]; simpl; intros y T H X HX.
  - discriminate H.
  - simpl in H. destruct (Nat.eqb y z) eqn:E.
    + apply Nat.eqb_eq in E. subst y. injection H as ->.
      apply in_or_app. left. exact HX.
    + apply in_or_app. right. eapply IH; eassumption.
Qed.

Definition update_ut (x : atom) (v : ut) (gamma : atom -> ut) : atom -> ut :=
  fun y => if Nat.eqb y x then v else gamma y.

Lemma update_ut_eq : forall x v gamma, update_ut x v gamma x = v.
Proof. intros. unfold update_ut. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_ut_neq : forall x y v gamma,
    y <> x -> update_ut x v gamma y = gamma y.
Proof.
  intros. unfold update_ut.
  assert (E : (y =? x) = false) by (apply Nat.eqb_neq; exact H).
  rewrite E. reflexivity.
Qed.

Definition update_sigma (X : atom) (S : cand) (sigma : atom -> cand) : atom -> cand :=
  fun Y => if Nat.eqb Y X then S else sigma Y.

Lemma update_sigma_eq : forall X S sigma, update_sigma X S sigma X = S.
Proof. intros. unfold update_sigma. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma update_sigma_neq : forall X Y S sigma,
    Y <> X -> update_sigma X S sigma Y = sigma Y.
Proof.
  intros. unfold update_sigma.
  assert (E : (Y =? X) = false) by (apply Nat.eqb_neq; exact H).
  rewrite E. reflexivity.
Qed.

Lemma subst_ut_ext : forall gamma1 gamma2 t,
    (forall y, In y (free_ut t) -> gamma1 y = gamma2 y) ->
    subst_ut gamma1 t = subst_ut gamma2 t.
Proof.
  intros gamma1 gamma2 t. revert gamma1 gamma2.
  induction t as
    [ i | a | b IHabs | t1 IH1 t2 IH2 | b IHtabs | b IHtapp | | b IHsucc
    | n IHn b IHb s IHs ];
    simpl; intros gamma1 gamma2 H.
  - reflexivity.
  - apply H. simpl. auto.
  - (* abs *) rewrite (IHabs gamma1 gamma2); [reflexivity |].
    intros y Hy. apply H. simpl. exact Hy.
  - (* app *)
    assert (E1 : subst_ut gamma1 t1 = subst_ut gamma2 t1).
    { apply IH1. intros y Hy. apply H. simpl. apply in_or_app. left. exact Hy. }
    assert (E2 : subst_ut gamma1 t2 = subst_ut gamma2 t2).
    { apply IH2. intros y Hy. apply H. simpl. apply in_or_app. right. exact Hy. }
    rewrite E1, E2. reflexivity.
  - (* tabs *) rewrite (IHtabs gamma1 gamma2); [reflexivity |].
    intros y Hy. apply H. simpl. exact Hy.
  - (* tapp *) rewrite (IHtapp gamma1 gamma2); [reflexivity |].
    intros y Hy. apply H. simpl. exact Hy.
  - reflexivity.
  - (* succ *) rewrite (IHsucc gamma1 gamma2); [reflexivity |].
    intros y Hy. apply H. simpl. exact Hy.
  - (* natrec *)
    assert (E1 : subst_ut gamma1 n = subst_ut gamma2 n).
    { apply IHn. intros y Hy. apply H. simpl. apply in_or_app. left. exact Hy. }
    assert (E2 : subst_ut gamma1 b = subst_ut gamma2 b).
    { apply IHb. intros y Hy. apply H. simpl. apply in_or_app. right.
      apply in_or_app. left. exact Hy. }
    assert (E3 : subst_ut gamma1 s = subst_ut gamma2 s).
    { apply IHs. intros y Hy. apply H. simpl. apply in_or_app. right.
      apply in_or_app. right. exact Hy. }
    rewrite E1, E2, E3. reflexivity.
Qed.

Lemma subst_ut_id : forall t, subst_ut (fun x => u_fvar x) t = t.
Proof.
  induction t; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma subst_ut_open_fvar : forall gamma,
    (forall y, lc_ut (gamma y)) ->
    forall k x t,
      subst_ut gamma (open_ut_rec k (u_fvar x) t) =
      open_ut_rec k (gamma x) (subst_ut gamma t).
Proof.
  intros gamma Hlc k x t. revert k.
  induction t; intros k; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite (lc_ut_at_open_id (gamma a) 0 (Hlc a) k (gamma x) (Nat.le_0_l k)).
    reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H as
    [ Delta X Hin
    | Delta T1 T2 H1 IH1 H2 IH2
    | L Delta T Hsub IHsub
    | Delta ].
  - constructor.
  - constructor; assumption.
  - apply lc_ty_all.
    pose proof (IHsub (fresh_atom L) (fresh_atom_notin L)) as HX.
    pose proof (lc_ty_open_inv T 0 0 (fresh_atom L) HX) as HT.
    simpl in HT. exact HT.
  - constructor.
Qed.

Lemma has_type_lc_ty : forall Delta Gamma t T,
    has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H. induction H as
    [ Delta Gamma x T Hlookup Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hsub IHsub
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hsub IHsub
    | Delta Gamma t T U H1 IH1 HwfU
    | Delta Gamma
    | Delta Gamma n Hn IHn
    | Delta Gamma n b s T Hn IHn Hb IHb Hs IHs ].
  - exact (wf_ty_lc Delta T Hwf).
  - constructor.
    + exact (wf_ty_lc Delta T1 Hwf).
    + apply (IHsub (fresh_atom L) (fresh_atom_notin L)).
  - apply lc_ty_at_arrow_inv_2 with (T1 := T1). exact IH1.
  - apply lc_ty_all.
    pose proof (IHsub (fresh_atom L) (fresh_atom_notin L)) as HX.
    pose proof (lc_ty_open_inv T 0 0 (fresh_atom L) HX) as HT.
    simpl in HT. exact HT.
  - apply lc_ty_open_fwd with (k := 0) (U := U).
    + apply lc_ty_at_all_inv. exact IH1.
    + exact (wf_ty_lc Delta U HwfU).
  - constructor.
  - exact IHn.
  - exact IHb.
Qed.


(* ---------- term environments and the fundamental theorem ---------- *)

Definition term_env (rho : nat -> cand) (sigma : atom -> cand)
    (gamma : atom -> ut) (Gamma : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> car (R_ty rho sigma T) (gamma x).

Lemma fundamental : forall Delta Gamma t T,
    has_type Delta Gamma t T ->
    forall rho sigma gamma,
      (forall y, lc_ut (gamma y)) ->
      term_env rho sigma gamma Gamma ->
      car (R_ty rho sigma T) (subst_ut gamma (erase t)).
Proof.
  intros Delta Gamma t T H. induction H as
    [ Delta Gamma x T Hlookup Hwf
    | L Delta Gamma T1 t2 T2 Hwf Hsub IHsub
    | Delta Gamma t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta Gamma t T Hsub IHsub
    | Delta Gamma t T U H1 IH1 HwfU
    | Delta Gamma
    | Delta Gamma n Hn IHn
    | Delta Gamma n b s T Hn IHn Hb IHb Hs IHs ].
  - (* T_Var *) intros rho sigma gamma Hlcg Henv. simpl. apply Henv. exact Hlookup.
  - (* T_Abs *)
    intros rho sigma gamma Hlcg Henv. simpl.
    set (eb := subst_ut gamma (erase t2)).
    set (x := fresh_atom (L ++ free_ut (erase t2))).
    assert (Hxnot : ~ In x (L ++ free_ut (erase t2))) by (unfold x; apply fresh_atom_notin).
    assert (HxL : ~ In x L).
    { intro H. apply Hxnot. apply in_or_app. left. exact H. }
    assert (Hxfree : ~ In x (free_ut (erase t2))).
    { intro H. apply Hxnot. apply in_or_app. right. exact H. }
    assert (Hlc_abs : lc_ut (u_abs eb)).
    { set (gamma0 := update_ut x (u_fvar x) gamma).
      assert (Hlcg0 : forall y, lc_ut (gamma0 y)).
      { intro y. unfold gamma0. destruct (Nat.eqb y x) eqn:E.
        - apply Nat.eqb_eq in E. subst y. rewrite update_ut_eq. simpl. exact I.
        - apply Nat.eqb_neq in E. rewrite (update_ut_neq x y (u_fvar x) gamma E).
          apply Hlcg. }
      assert (Henv0 : term_env rho sigma gamma0 ((x, T1) :: Gamma)).
      { intros y Ty Hlook. simpl in Hlook.
        destruct (Nat.eqb y x) eqn:E.
        - unfold gamma0, update_ut. rewrite E. simpl. apply fvar_cand.
        - unfold gamma0, update_ut. rewrite E. simpl. apply Henv. exact Hlook. }
      pose proof (IHsub x HxL rho sigma gamma0 Hlcg0 Henv0) as Hopen.
      rewrite erase_open_tm in Hopen.
      simpl in Hopen. unfold open_ut in Hopen.
      rewrite (subst_ut_open_fvar gamma0 Hlcg0 0 x (erase t2)) in Hopen.
      assert (Hgx : gamma0 x = u_fvar x) by (unfold gamma0; apply update_ut_eq).
      rewrite Hgx in Hopen.
      assert (Hsubst_eq : subst_ut gamma0 (erase t2) = subst_ut gamma (erase t2)).
      { apply subst_ut_ext. intros y Hy. apply update_ut_neq.
        intro Hxy. apply Hxfree. subst y. exact Hy. }
      rewrite Hsubst_eq in Hopen.
      change (car (R_ty rho sigma T2) (open_ut eb (u_fvar x))) in Hopen.
      pose proof (cand_lc (R_ty rho sigma T2) (open_ut eb (u_fvar x)) Hopen) as Hlcopen.
      pose proof (lc_ut_open_inv eb 0 0 x Hlcopen) as Hlc1.
      simpl in Hlc1. simpl. exact Hlc1. }
    unfold arrow_cand. simpl.
    split; [|split].
    + apply value_ut_SN. apply value_abs.
    + exact Hlc_abs.
    + intros v HAv.
      apply (abs_app_red eb (R_ty rho sigma T1) (R_ty rho sigma T2) Hlc_abs).
      * intros u HAu.
        set (gammau := update_ut x u gamma).
        assert (Hlcgu : forall y, lc_ut (gammau y)).
        { intro y. unfold gammau. destruct (Nat.eqb y x) eqn:E.
          - apply Nat.eqb_eq in E. subst y. rewrite update_ut_eq.
            apply (cand_lc (R_ty rho sigma T1) u HAu).
          - apply Nat.eqb_neq in E. rewrite (update_ut_neq x y u gamma E).
            apply Hlcg. }
        assert (Henvu : term_env rho sigma gammau ((x, T1) :: Gamma)).
        { intros y Ty Hlook. simpl in Hlook.
          destruct (Nat.eqb y x) eqn:E.
          - injection Hlook as Hty. subst Ty. unfold gammau, update_ut. rewrite E. simpl. exact HAu.
          - unfold gammau, update_ut. rewrite E. simpl. apply Henv. exact Hlook. }
        pose proof (IHsub x HxL rho sigma gammau Hlcgu Henvu) as Hg.
        rewrite erase_open_tm in Hg.
        simpl in Hg. unfold open_ut in Hg.
        rewrite (subst_ut_open_fvar gammau Hlcgu 0 x (erase t2)) in Hg.
        assert (Hgx : gammau x = u) by (unfold gammau; apply update_ut_eq).
        rewrite Hgx in Hg.
        assert (Hsubst_u : subst_ut gammau (erase t2) = subst_ut gamma (erase t2)).
        { apply subst_ut_ext. intros y Hy. apply update_ut_neq.
          intro Hxy. apply Hxfree. subst y. exact Hy. }
        rewrite Hsubst_u in Hg.
        change (car (R_ty rho sigma T2) (open_ut eb u)) in Hg.
        exact Hg.
      * apply (cand_sn (R_ty rho sigma T1) v HAv).
      * exact HAv.
  - (* T_App *)
    intros rho sigma gamma Hlcg Henv. simpl.
    pose proof (IH1 rho sigma gamma Hlcg Henv) as H1'.
    pose proof (IH2 rho sigma gamma Hlcg Henv) as H2'.
    apply (proj2 (proj2 H1')).
    exact H2'.
  - (* T_TAbs *)
    intros rho sigma gamma Hlcg Henv. simpl.
    set (eb := subst_ut gamma (erase t)).
    set (X := fresh_atom (L ++ (free_ty T ++ free_gamma Gamma))).
    assert (HXnot : ~ In X (L ++ (free_ty T ++ free_gamma Gamma)))
      by (unfold X; apply fresh_atom_notin).
    assert (HXL : ~ In X L).
    { intro H. apply HXnot. apply in_or_app. left. exact H. }
    assert (HXT : ~ In X (free_ty T)).
    { intro H. apply HXnot. apply in_or_app. right. apply in_or_app. left. exact H. }
    assert (HXG : ~ In X (free_gamma Gamma)).
    { intro H. apply HXnot. apply in_or_app. right. apply in_or_app. right. exact H. }
    pose proof (IHsub X HXL rho sigma gamma Hlcg Henv) as Hopen.
    rewrite erase_open_tm_ty in Hopen.
    change (car (R_ty rho sigma (open_ty T (Ty_FVar X))) eb) in Hopen.
    pose proof (cand_lc (R_ty rho sigma (open_ty T (Ty_FVar X))) eb Hopen) as Hlceb.
    unfold all_cand. simpl.
    split; [|split].
    + apply value_ut_SN. apply value_tabs.
    + exact Hlceb.
    + intros Sc.
      set (sigmaX := update_sigma X Sc sigma).
      assert (HenvX : term_env rho sigmaX gamma Gamma).
      { intros y Ty Hlook.
        assert (Heq : forall Y, In Y (free_ty Ty) -> sigma Y = sigmaX Y).
        { intros Y HY. symmetry. apply update_sigma_neq. intro HYX. subst Y.
          apply HXG. eapply free_gamma_in; eassumption. }
        apply (proj1 (R_ty_sigma_rel Ty rho sigma sigmaX Heq (gamma y))).
        apply Henv. exact Hlook. }
      pose proof (IHsub X HXL rho sigmaX gamma Hlcg HenvX) as HopenX.
      rewrite erase_open_tm_ty in HopenX.
      change (car (R_ty rho sigmaX (open_ty T (Ty_FVar X))) eb) in HopenX.
      pose proof (has_type_lc_ty _ _ _ _ (Hsub X HXL)) as HlcTyOpen.
      pose proof (lc_ty_open_inv T 0 0 X HlcTyOpen) as HT1.
      simpl in HT1.
      pose proof (R_ty_open_gen T 0 (Ty_FVar X) rho sigmaX (lc_ty_fvar 0 X) HT1 eb) as HsubstTy.
      apply HsubstTy in HopenX.
      assert (HsigmaX : R_ty rho sigmaX (Ty_FVar X) = Sc).
      { simpl. unfold sigmaX. apply update_sigma_eq. }
      rewrite HsigmaX in HopenX.
      assert (Hagree : forall i, i < 1 -> forall z,
          car ((replace_at 0 Sc rho) i) z <-> car ((cons_cand Sc rho) i) z).
      { intros i Hi z. destruct i as [| i]; [simpl; reflexivity | lia]. }
      assert (HopenC : car (R_ty (cons_cand Sc rho) sigmaX T) eb).
      { apply (proj1 (R_ty_env_rel T 1 HT1 (replace_at 0 Sc rho) (cons_cand Sc rho) sigmaX Hagree eb)).
        exact HopenX. }
      assert (HeqT : forall Y, In Y (free_ty T) -> sigma Y = sigmaX Y).
      { intros Y HY. symmetry. apply update_sigma_neq. intro HYX. subst Y.
        apply HXT. exact HY. }
      assert (HopenS : car (R_ty (cons_cand Sc rho) sigma T) eb).
      { apply (proj2 (R_ty_sigma_rel T (cons_cand Sc rho) sigma sigmaX HeqT eb)). exact HopenC. }
      apply (cand_back (R_ty (cons_cand Sc rho) sigma T) (u_tapp (u_tabs eb)) eb).
      * simpl. exact Hlceb.
      * apply ustep_tapp_tabs.
      * exact HopenS.
  - (* T_TApp *)
    intros rho sigma gamma Hlcg Henv. simpl.
    pose proof (IH1 rho sigma gamma Hlcg Henv) as H1'.
    set (e := subst_ut gamma (erase t)).
    change (car (R_ty rho sigma (open_ty_rec 0 U T)) (u_tapp e)).
    set (Sc := R_ty rho sigma U).
    assert (Hall : car (R_ty (cons_cand Sc rho) sigma T) (u_tapp e)).
    { apply (proj2 (proj2 H1')). }
    pose proof (has_type_lc_ty _ _ _ _ H1) as HlcAll.
    pose proof (lc_ty_at_all_inv 0 T HlcAll) as HT1.
    pose proof (wf_ty_lc Delta U HwfU) as HU.
    pose proof (R_ty_open_gen T 0 U rho sigma HU HT1 (u_tapp e)) as Hsub.
    apply (proj2 Hsub).
    assert (Hagree : forall i, i < 1 -> forall z,
        car ((replace_at 0 Sc rho) i) z <-> car ((cons_cand Sc rho) i) z).
    { intros i Hi z. destruct i as [| i]; [simpl; reflexivity | lia]. }
    apply (proj2 (R_ty_env_rel T 1 HT1 (replace_at 0 Sc rho) (cons_cand Sc rho) sigma Hagree (u_tapp e))).
    exact Hall.
  - (* T_Zero *)
    intros rho sigma gamma Hlcg Henv. simpl.
    split.
    + apply value_ut_SN. apply value_num. constructor.
    + simpl. exact I.
  - (* T_Succ *)
    intros rho sigma gamma Hlcg Henv. simpl.
    pose proof (IHn rho sigma gamma Hlcg Henv) as Hn'.
    destruct Hn' as [Hsn Hlc].
    split.
    + apply SN_ut_succ. exact Hsn.
    + simpl. exact Hlc.
  - (* T_Rec *)
    intros rho sigma gamma Hlcg Henv. simpl.
    pose proof (IHn rho sigma gamma Hlcg Henv) as Hn'.
    pose proof (IHb rho sigma gamma Hlcg Henv) as Hb'.
    pose proof (IHs rho sigma gamma Hlcg Henv) as Hs'.
    apply (natrec_mem (R_ty rho sigma T)
             (subst_ut gamma (erase n)) (subst_ut gamma (erase b)) (subst_ut gamma (erase s))).
    + exact Hn'.
    + exact Hb'.
    + exact Hs'.
Qed.


Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  intros t T Hty.
  pose (rho0 := fun _ : nat => nat_cand).
  pose (sigma0 := fun _ : atom => nat_cand).
  pose (gamma0 := fun x : atom => u_fvar x).
  pose proof (fundamental [] empty t T Hty rho0 sigma0 gamma0) as Hfund.
  assert (Hlcg0 : forall y, lc_ut (gamma0 y)).
  { intros y. simpl. exact I. }
  assert (Henv0 : term_env rho0 sigma0 gamma0 empty).
  { intros x Ty Hlook. simpl in Hlook. discriminate Hlook. }
  specialize (Hfund Hlcg0 Henv0).
  assert (Hsubst : subst_ut gamma0 (erase t) = erase t).
  { apply subst_ut_id. }
  rewrite Hsubst in Hfund.
  assert (HSN : SN_ut (erase t)).
  { apply (cand_sn (R_ty rho0 sigma0 T) (erase t)). exact Hfund. }
  exact (SN_annot_of_SN_ut (erase t) HSN t eq_refl).
Qed.

End SystemFNormalizationRecursionHardTask.
