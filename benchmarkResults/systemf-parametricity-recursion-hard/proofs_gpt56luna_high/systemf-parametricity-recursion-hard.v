(** System F parametricity benchmark, Hard variant.
    Features: recursion. *)

From Stdlib Require Import Arith.PeanoNat Lists.List Lia.
Import ListNotations.

Module SystemFParametricityRecursionHardTask.

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


Hint Constructors lc_ty_at lc_tm_at value : core.

(* The relation below is deliberately a relation on values, rather than on
   arbitrary terms.  This is the useful choice for the call-by-value
   semantics in this file: its expression closure says that both expressions
   have a common related pair of value results. *)
Definition vrel := tm -> tm -> Prop.

Record ty_entry : Type :=
  { te_name : atom;
    te_left : ty;
    te_right : ty;
    te_vrel : vrel }.

Definition ty_env := list ty_entry.

Fixpoint lookup_ty_env (X : atom) (E : ty_env) : option ty_entry :=
  match E with
  | [] => None
  | e :: E' => if Nat.eqb X (te_name e) then Some e else lookup_ty_env X E'
  end.

Definition ty_env_extend (E : ty_env) (X : atom) (A B : ty) (R : vrel) : ty_env :=
  {| te_name := X; te_left := A; te_right := B; te_vrel := R |} :: E.

Fixpoint ty_inst_left (E : ty_env) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X =>
      match lookup_ty_env X E with
      | Some e => te_left e
      | None => Ty_FVar X
      end
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_inst_left E T1) (ty_inst_left E T2)
  | Ty_All T1 => Ty_All (ty_inst_left E T1)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint ty_inst_right (E : ty_env) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X =>
      match lookup_ty_env X E with
      | Some e => te_right e
      | None => Ty_FVar X
      end
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_inst_right E T1) (ty_inst_right E T2)
  | Ty_All T1 => Ty_All (ty_inst_right E T1)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint tm_inst_left (E : ty_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_inst_left E T) (tm_inst_left E t1)
  | tm_app t1 t2 => tm_app (tm_inst_left E t1) (tm_inst_left E t2)
  | tm_tabs t1 => tm_tabs (tm_inst_left E t1)
  | tm_tapp t1 T => tm_tapp (tm_inst_left E t1) (ty_inst_left E T)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_inst_left E t1)
  | tm_natrec n b s => tm_natrec (tm_inst_left E n) (tm_inst_left E b) (tm_inst_left E s)
  end.

Fixpoint tm_inst_right (E : ty_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T t1 => tm_abs (ty_inst_right E T) (tm_inst_right E t1)
  | tm_app t1 t2 => tm_app (tm_inst_right E t1) (tm_inst_right E t2)
  | tm_tabs t1 => tm_tabs (tm_inst_right E t1)
  | tm_tapp t1 T => tm_tapp (tm_inst_right E t1) (ty_inst_right E T)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_inst_right E t1)
  | tm_natrec n b s => tm_natrec (tm_inst_right E n) (tm_inst_right E b) (tm_inst_right E s)
  end.

Definition tm_env := list (atom * tm).

Fixpoint lookup_tm_env (x : atom) (E : tm_env) : option tm :=
  match E with
  | [] => None
  | (y,t) :: E' => if Nat.eqb x y then Some t else lookup_tm_env x E'
  end.

Fixpoint tm_subst_env (S : tm_env) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x =>
      match lookup_tm_env x S with
      | Some u => u
      | None => tm_fvar x
      end
  | tm_abs T t1 => tm_abs T (tm_subst_env S t1)
  | tm_app t1 t2 => tm_app (tm_subst_env S t1) (tm_subst_env S t2)
  | tm_tabs t1 => tm_tabs (tm_subst_env S t1)
  | tm_tapp t1 T => tm_tapp (tm_subst_env S t1) T
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_subst_env S t1)
  | tm_natrec n b s => tm_natrec (tm_subst_env S n) (tm_subst_env S b) (tm_subst_env S s)
  end.

Definition close_left (E : ty_env) (S : tm_env) (t : tm) : tm :=
  tm_inst_left E (tm_subst_env S t).
Definition close_right (E : ty_env) (S : tm_env) (t : tm) : tm :=
  tm_inst_right E (tm_subst_env S t).

Definition expr_rel (I : ty -> vrel) (T : ty) (t1 t2 : tm) : Prop :=
  exists v1 v2,
    t1 -->* v1 /\ t2 -->* v2 /\ value v1 /\ value v2 /\ I T v1 v2.

Fixpoint ty_atoms (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_atoms T1 ++ ty_atoms T2
  | Ty_All T1 => ty_atoms T1
  | Ty_Nat => []
  end.

Fixpoint tm_atoms (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T t1 => ty_atoms T ++ tm_atoms t1
  | tm_app t1 t2 => tm_atoms t1 ++ tm_atoms t2
  | tm_tabs t1 => tm_atoms t1
  | tm_tapp t1 T => tm_atoms t1 ++ ty_atoms T
  | tm_zero => []
  | tm_succ t1 => tm_atoms t1
  | tm_natrec n b s => tm_atoms n ++ tm_atoms b ++ tm_atoms s
  end.

Fixpoint type_rel (F : list atom) (E : ty_env) (B : list vrel) (T : ty) : vrel :=
  match T with
  | Ty_BVar i =>
      match nth_error B i with
      | Some R => R
      | None => fun _ _ => False
      end
  | Ty_FVar X =>
      match lookup_ty_env X E with
      | Some e => te_vrel e
      | None => fun _ _ => False
      end
  | Ty_Arrow T1 T2 =>
      fun f1 f2 =>
        forall a1 a2, value a1 -> value a2 ->
          expr_rel (type_rel F E B) T1 a1 a2 ->
          expr_rel (type_rel F E B) T2 (tm_app f1 a1) (tm_app f2 a2)
  | Ty_All T1 =>
      fun q1 q2 =>
        match q1, q2 with
        | tm_tabs b1, tm_tabs b2 =>
            forall A1 A2 R, exists X,
              ~ In X (F ++ tm_atoms b1 ++ tm_atoms b2) /\
              expr_rel (type_rel F (ty_env_extend E X A1 A2 R) (R :: B))
                T1
                (close_left (ty_env_extend E X A1 A2 R) []
                  (open_tm_ty b1 (Ty_FVar X)))
                (close_right (ty_env_extend E X A1 A2 R) []
                  (open_tm_ty b2 (Ty_FVar X)))
        | _, _ => False
        end
  | Ty_Nat => fun n1 n2 => n1 = n2
  end.

Definition exp_rel (F : list atom) (E : ty_env) (B : list vrel) (T : ty)
           (t1 t2 : tm) : Prop :=
  expr_rel (type_rel F E B) T t1 t2.

Definition ctx_rel (F : list atom) (E : ty_env) (B : list vrel)
           (Gamma : context) (S1 S2 : tm_env) : Prop :=
  forall x T, lookup_context x Gamma = Some T ->
    exp_rel F E B T (close_left E S1 (tm_fvar x))
                     (close_right E S2 (tm_fvar x)).

Fixpoint atom_max (L : list atom) : atom :=
  match L with
  | [] => 0
  | x :: L' => Nat.max x (atom_max L')
  end.

Lemma atom_le_max : forall x L, In x L -> x <= atom_max L.
Proof.
  induction L as [|y L IH]; simpl; intros H.
  - contradiction.
  - destruct H as [<-|H].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact H|apply Nat.le_max_r].
Qed.

Lemma fresh_atom : forall (L : list atom), exists x, ~ In x L.
Proof.
  intro L. exists (S (atom_max L)).
  intro H. pose proof (atom_le_max _ _ H). lia.
Qed.

Lemma lc_ty_open_inv : forall k T X,
    lc_ty_at k (open_ty_rec k (Ty_FVar X) T) ->
    lc_ty_at (S k) T.
Proof.
  intros k T X H. revert k X H. induction T; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:He.
    + constructor; apply Nat.eqb_eq in He; lia.
    + inversion H; constructor; lia.
  - inversion H; constructor.
  - inversion H; constructor; eauto.
  - inversion H. constructor. eapply IHT; eauto.
  - inversion H; constructor.
Qed.

Lemma wf_ty_lc : forall D T, wf_ty D T -> locally_closed_ty T.
Proof.
  intros D T H.
  induction H as
    [D X Hin
    |D T1 T2 H1 IH1 H2 IH2
    |L D T H IH
    |D].
  - constructor.
  - constructor; assumption.
  - constructor. destruct (fresh_atom L) as [X HX].
    specialize (H X HX). apply (lc_ty_open_inv 0 T X).
    apply IH. exact HX.
  - constructor.
Qed.

Lemma lc_ty_open_rec_inv_at : forall k K T X,
    k < K -> lc_ty_at K (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at K T.
Proof.
  intros k K T X Hk. revert k K X Hk. induction T; intros k K X Hk Hlc; simpl in *.
  - destruct (Nat.eqb k n) eqn:He.
    + apply lc_ty_bvar; apply Nat.eqb_eq in He; lia.
    + inversion Hlc; apply lc_ty_bvar; lia.
  - inversion Hlc; constructor.
  - inversion Hlc; constructor; eauto.
  - inversion Hlc. constructor.
    eapply IHT with (k := S k) (K := S K) (X := X); eauto; lia.
  - inversion Hlc; constructor.
Qed.

Lemma lc_tm_open_inv : forall K k t x,
    lc_tm_at K k (open_tm_rec k (tm_fvar x) t) ->
    lc_tm_at K (S k) t.
Proof.
  intros K k t x H. revert K k x H. induction t; intros K k x H; simpl in H.
  - destruct (Nat.eqb k n) eqn:He.
    + constructor; apply Nat.eqb_eq in He; lia.
    + inversion H; constructor; lia.
  - inversion H; constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
  - constructor.
  - inversion H; constructor; eauto.
  - inversion H; constructor; eauto.
Qed.

Lemma multi_trans : forall a b c, a -->* b -> b -->* c -> a -->* c.
Proof.
  intros a b c Hab Hbc. induction Hab.
  - exact Hbc.
  - eapply multi_step; eauto.
Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v Hv. destruct Hv.
  - exact H.
  - exact H.
  - apply numeric_value_lc; assumption.
Qed.

Lemma multi_app_left : forall t t' u,
    t -->* t' -> locally_closed_tm u ->
    tm_app t u -->* tm_app t' u.
Proof.
  intros t t' u H. induction H; intros Hu.
  - constructor.
  - eapply multi_step.
    + eapply ST_App1; eauto.
    + apply IHmulti; exact Hu.
Qed.

Lemma multi_app_right : forall v t t',
    value v -> t -->* t' ->
    tm_app v t -->* tm_app v t'.
Proof.
  intros v t t' Hv H. induction H.
  - constructor.
  - eapply multi_step.
    + eapply ST_App2; eauto.
    + exact IHmulti.
Qed.

Lemma multi_tapp_left : forall t t' T,
    t -->* t' -> locally_closed_ty T ->
    tm_tapp t T -->* tm_tapp t' T.
Proof.
  intros t t' T H HT. induction H.
  - constructor.
  - eapply multi_step; eauto using ST_TApp.
Qed.

Lemma multi_succ : forall t t', t -->* t' -> tm_succ t -->* tm_succ t'.
Proof.
  intros t t' H. induction H.
  - constructor.
  - eapply multi_step; eauto using ST_Succ.
Qed.

Lemma multi_rec_arg : forall n n' b s,
    n -->* n' -> locally_closed_tm b -> locally_closed_tm s ->
    tm_natrec n b s -->* tm_natrec n' b s.
Proof.
  intros n n' b s H. induction H; intros Hb Hs.
  - constructor.
  - eapply multi_step.
    + eapply ST_RecArg; eauto.
    + apply IHmulti; assumption.
Qed.

Lemma multi_rec_base : forall n b b' s,
    numeric_value n -> b -->* b' -> locally_closed_tm s ->
    tm_natrec n b s -->* tm_natrec n b' s.
Proof.
  intros n b b' s Hn H. induction H; intros Hs.
  - constructor.
  - eapply multi_step.
    + eapply ST_RecBase; eauto.
    + apply IHmulti; assumption.
Qed.

Lemma multi_rec_step : forall n b s s',
    numeric_value n -> value b -> s -->* s' ->
    tm_natrec n b s -->* tm_natrec n b s'.
Proof.
  intros n b s s' Hn Hb H. induction H.
  - constructor.
  - eapply multi_step.
    + eapply ST_RecStep; eauto.
    + exact IHmulti.
Qed.

Lemma exp_rel_intro : forall I T t1 t2 v1 v2,
    t1 -->* v1 -> t2 -->* v2 -> value v1 -> value v2 ->
    I T v1 v2 -> expr_rel I T t1 t2.
Proof.
  intros; repeat eexists; eauto.
Qed.

Lemma exp_rel_morph : forall I J T t1 t2,
    (forall a b, I T a b <-> J T a b) ->
    expr_rel I T t1 t2 -> expr_rel J T t1 t2.
Proof.
  intros I J T t1 t2 H [v1 [v2 [H1 [H2 [Hv1 [Hv2 HR]]]]]].
  apply (exp_rel_intro J T t1 t2 v1 v2 H1 H2 Hv1 Hv2).
  now apply (H v1 v2).
Qed.

Lemma exp_rel_app : forall F E B T1 T2 f1 f2 a1 a2,
    exp_rel F E B (Ty_Arrow T1 T2) f1 f2 ->
    locally_closed_tm a1 -> locally_closed_tm a2 ->
    exp_rel F E B T1 a1 a2 ->
    exp_rel F E B T2 (tm_app f1 a1) (tm_app f2 a2).
Proof.
  intros F E B T1 T2 f1 f2 a1 a2
    [vf1 [vf2 [Hf1 [Hf2 [Hvf1 [Hvf2 Hfr]]]]]]
    Hlc1 Hlc2
    [va1 [va2 [Ha1 [Ha2 [Hva1 [Hva2 Har]]]]]].
  specialize (Hfr va1 va2 Hva1 Hva2
    (exp_rel_intro (type_rel F E B) T1 va1 va2 va1 va2
      (multi_refl _) (multi_refl _) Hva1 Hva2 Har)).
  destruct Hfr as [z1 [z2 [Hz1 [Hz2 [Hzv1 [Hzv2 Hz]]]]]].
  assert (Hl1 : tm_app f1 a1 -->* tm_app vf1 a1).
  { apply multi_app_left; assumption. }
  assert (Hr1 : tm_app vf1 a1 -->* tm_app vf1 va1).
  { apply multi_app_right; assumption. }
  assert (Hl2 : tm_app f2 a2 -->* tm_app vf2 a2).
  { apply multi_app_left; assumption. }
  assert (Hr2 : tm_app vf2 a2 -->* tm_app vf2 va2).
  { apply multi_app_right; assumption. }
  apply (exp_rel_intro _ _ _ _ z1 z2).
  - eapply multi_trans; [exact Hl1 | eapply multi_trans; [exact Hr1 | exact Hz1]].
  - eapply multi_trans; [exact Hl2 | eapply multi_trans; [exact Hr2 | exact Hz2]].
  - exact Hzv1.
  - exact Hzv2.
  - exact Hz.
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
  intros t H U v HU Hv HvT.
  induction H; simpl in *; eauto.
  all: idtac.
Qed.

End SystemFParametricityRecursionHardTask.
