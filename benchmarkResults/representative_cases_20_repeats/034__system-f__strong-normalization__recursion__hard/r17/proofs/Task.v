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
(* Infrastructure: free atoms, freshness, canonicalization,     *)
(* simultaneous type substitution and term substitution.        *)
(* ============================================================ *)

Fixpoint fv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => fv_ty T1 ++ fv_ty T2
  | Ty_All T1 => fv_ty T1
  | Ty_Nat => []
  end.

Fixpoint fv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T b => fv_ty T ++ fv_tm b
  | tm_app t1 t2 => fv_tm t1 ++ fv_tm t2
  | tm_tabs b => fv_tm b
  | tm_tapp t1 T => fv_tm t1 ++ fv_ty T
  | tm_zero => []
  | tm_succ t => fv_tm t
  | tm_natrec n b s => fv_tm n ++ fv_tm b ++ fv_tm s
  end.

Fixpoint max_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: l' => Nat.max x (max_list l')
  end.

Lemma max_list_spec : forall l x, In x l -> x <= max_list l.
Proof.
  induction l as [|y l IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [<- | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH, Hin | apply Nat.le_max_r].
Qed.

Definition fresh_atom (l : list atom) : atom := S (max_list l).

Lemma fresh_atom_not_in : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l Hin. unfold fresh_atom in Hin.
  pose proof (max_list_spec l _ Hin). lia.
Qed.

(* Erase all type annotations; type arguments become Nat. *)
Fixpoint canon (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs Ty_Nat (canon b)
  | tm_app t1 t2 => tm_app (canon t1) (canon t2)
  | tm_tabs b => tm_tabs (canon b)
  | tm_tapp t1 T => tm_tapp (canon t1) Ty_Nat
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (canon t)
  | tm_natrec n b s => tm_natrec (canon n) (canon b) (canon s)
  end.

Lemma canon_idem : forall t, canon (canon t) = canon t.
Proof. induction t; simpl; congruence. Qed.

(* Simultaneous substitution of free type variables by types. *)
Fixpoint tsubst_ty (tau : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => tau X
  | Ty_Arrow T1 T2 => Ty_Arrow (tsubst_ty tau T1) (tsubst_ty tau T2)
  | Ty_All T1 => Ty_All (tsubst_ty tau T1)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint tsubst_tm (tau : atom -> ty) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs T b => tm_abs (tsubst_ty tau T) (tsubst_tm tau b)
  | tm_app t1 t2 => tm_app (tsubst_tm tau t1) (tsubst_tm tau t2)
  | tm_tabs b => tm_tabs (tsubst_tm tau b)
  | tm_tapp t1 T => tm_tapp (tsubst_tm tau t1) (tsubst_ty tau T)
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (tsubst_tm tau t)
  | tm_natrec n b s =>
      tm_natrec (tsubst_tm tau n) (tsubst_tm tau b) (tsubst_tm tau s)
  end.

(* Simultaneous substitution of free term variables by terms. *)
Fixpoint subst_env (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T b => tm_abs T (subst_env sigma b)
  | tm_app t1 t2 => tm_app (subst_env sigma t1) (subst_env sigma t2)
  | tm_tabs b => tm_tabs (subst_env sigma b)
  | tm_tapp t1 T => tm_tapp (subst_env sigma t1) T
  | tm_zero => tm_zero
  | tm_succ t => tm_succ (subst_env sigma t)
  | tm_natrec n b s =>
      tm_natrec (subst_env sigma n) (subst_env sigma b) (subst_env sigma s)
  end.

Definition upd_tau (tau : atom -> ty) (X : atom) (U : ty) : atom -> ty :=
  fun Y => if Nat.eqb Y X then U else tau Y.

Definition upd_env (sigma : atom -> tm) (x : atom) (u : tm) : atom -> tm :=
  fun y => if Nat.eqb y x then u else sigma y.

Lemma subst_env_id : forall t, subst_env (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; congruence. Qed.

Lemma open_ty_rec_lc_id_gen : forall K0 T K U,
  lc_ty_at K0 T -> K0 <= K -> open_ty_rec K U T = T.
Proof.
  intros K0 T. revert K0. induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 | ]; intros K0 K U Hlc Hle; simpl.
  - destruct (Nat.eqb K n) eqn:E.
    + apply Nat.eqb_eq in E. inversion Hlc; subst. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal; [eapply IH1; eassumption | eapply IH2; eassumption].
  - inversion Hlc; subst. f_equal. eapply IH1; [eassumption|lia].
  - reflexivity.
Qed.

Lemma open_tm_ty_rec_lc_id_gen : forall K0 k t K U,
  lc_tm_at K0 k t -> K0 <= K -> open_tm_ty_rec K U t = t.
Proof.
  intros K0 k t. revert K0 k. induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss]; intros K0 k K U Hlc Hle; simpl.
  - reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal.
    + eapply open_ty_rec_lc_id_gen; eassumption.
    + eapply IHb; eassumption.
  - inversion Hlc; subst. f_equal; [eapply IH1; eassumption | eapply IH2; eassumption].
  - inversion Hlc; subst. f_equal. eapply IHb; [eassumption|lia].
  - inversion Hlc; subst. f_equal.
    + eapply IH1; eassumption.
    + eapply open_ty_rec_lc_id_gen; eassumption.
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHb; eassumption.
  - inversion Hlc; subst. f_equal; [eapply IHnn; eassumption | eapply IHbb; eassumption | eapply IHss; eassumption].
Qed.

Lemma open_tm_rec_lc_id_gen : forall K k t j u,
  lc_tm_at K k t -> k <= j -> open_tm_rec j u t = t.
Proof.
  intros K k t. revert K k. induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss]; intros K k j u Hlc Hle; simpl.
  - destruct (Nat.eqb j i) eqn:E.
    + apply Nat.eqb_eq in E. inversion Hlc; subst. lia.
    + reflexivity.
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHb; [eassumption|lia].
  - inversion Hlc; subst. f_equal; [eapply IH1; eassumption | eapply IH2; eassumption].
  - inversion Hlc; subst. f_equal. eapply IHb; eassumption.
  - inversion Hlc; subst. f_equal. eapply IH1; eassumption.
  - reflexivity.
  - inversion Hlc; subst. f_equal. eapply IHb; eassumption.
  - inversion Hlc; subst. f_equal; [eapply IHnn; eassumption | eapply IHbb; eassumption | eapply IHss; eassumption].
Qed.

Lemma open_tm_rec_lc_id : forall t j u,
  locally_closed_tm t -> open_tm_rec j u t = t.
Proof.
  intros. apply open_tm_rec_lc_id_gen with (K := 0) (k := 0); auto. lia.
Qed.

Lemma open_tm_ty_rec_lc_id : forall t K U,
  locally_closed_tm t -> open_tm_ty_rec K U t = t.
Proof.
  intros. apply open_tm_ty_rec_lc_id_gen with (K0 := 0) (k := 0); auto. lia.
Qed.

Lemma subst_env_open_tm_rec : forall k u t sigma,
  (forall x, locally_closed_tm (sigma x)) ->
  subst_env sigma (open_tm_rec k u t) =
  open_tm_rec k (subst_env sigma u) (subst_env sigma t).
Proof.
  intros k u t sigma Hsig. revert k u sigma Hsig.
  induction t; intros k u sigma Hsig; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - rewrite open_tm_rec_lc_id with (j := k) (u := subst_env sigma u); auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - reflexivity.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma tsubst_tm_open_tm_rec : forall tau k u t,
  tsubst_tm tau (open_tm_rec k u t) =
  open_tm_rec k (tsubst_tm tau u) (tsubst_tm tau t).
Proof.
  intros tau k u t. revert tau k u.
  induction t; intros tau k u; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt. reflexivity.
  - reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2, IHt3. reflexivity.
Qed.

Lemma tsubst_ty_open_ty_rec : forall tau k U T,
  (forall X, lc_ty_at 0 (tau X)) ->
  tsubst_ty tau (open_ty_rec k U T) =
  open_ty_rec k (tsubst_ty tau U) (tsubst_ty tau T).
Proof.
  intros tau k U T Htau. revert tau k U Htau.
  induction T; intros tau k U Htau; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. eapply open_ty_rec_lc_id_gen; [apply Htau | lia].
  - rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
  - reflexivity.
Qed.

Lemma tsubst_tm_open_tm_ty_rec : forall tau K U t,
  (forall X, lc_ty_at 0 (tau X)) ->
  tsubst_tm tau (open_tm_ty_rec K U t) =
  open_tm_ty_rec K (tsubst_ty tau U) (tsubst_tm tau t).
Proof.
  intros tau K U t Htau. revert tau K U Htau.
  induction t; intros tau K U Htau; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite tsubst_ty_open_ty_rec; auto. rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto. rewrite tsubst_ty_open_ty_rec; auto.
  - reflexivity.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

Lemma subst_env_open_tm_ty_rec : forall K U t sigma,
  (forall x, locally_closed_tm (sigma x)) ->
  subst_env sigma (open_tm_ty_rec K U t) =
  open_tm_ty_rec K U (subst_env sigma t).
Proof.
  intros K U t sigma Hsig. revert K U sigma Hsig.
  induction t; intros K U sigma Hsig; simpl.
  - reflexivity.
  - rewrite open_tm_ty_rec_lc_id with (K := K) (U := U); auto.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2; auto.
  - rewrite IHt; auto.
  - rewrite IHt; auto.
  - reflexivity.
  - rewrite IHt; auto.
  - rewrite IHt1, IHt2, IHt3; auto.
Qed.

(* ============================================================ *)
(* Locally-closed lemmas                                        *)
(* ============================================================ *)

Lemma lc_ty_at_weaken : forall k1 k2 T,
  k1 <= k2 -> lc_ty_at k1 T -> lc_ty_at k2 T.
Proof.
  intros k1 k2 T Hle H. revert k1 k2 Hle H.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 | ]; intros k1 k2 Hle H; inversion H; subst.
  - constructor. lia.
  - constructor.
  - constructor; [eapply IH1; eassumption | eapply IH2; eassumption].
  - constructor. apply IH1 with (k1 := S k1) (k2 := S k2); [lia|assumption].
  - constructor.
Qed.

Lemma lc_tm_at_weaken_K : forall K1 K2 k t,
  K1 <= K2 -> lc_tm_at K1 k t -> lc_tm_at K2 k t.
Proof.
  intros K1 K2 k t Hle H. revert K1 K2 k Hle H.
  induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    intros K1 K2 k Hle H; simpl in *; inversion H; subst.
  - constructor; assumption.
  - constructor.
  - constructor; [apply lc_ty_at_weaken with (k1:=K1); assumption | eapply IHb; eassumption].
  - constructor; [eapply IH1; eassumption | eapply IH2; eassumption].
  - constructor. apply IHb with (K1 := S K1) (K2 := S K2); [lia|assumption].
  - constructor; [eapply IH1; eassumption | apply lc_ty_at_weaken with (k1:=K1); assumption].
  - constructor.
  - constructor. eapply IHb; eassumption.
  - constructor; [eapply IHnn; eassumption | eapply IHbb; eassumption | eapply IHss; eassumption].
Qed.

Lemma lc_tm_at_weaken_k : forall K k1 k2 t,
  k1 <= k2 -> lc_tm_at K k1 t -> lc_tm_at K k2 t.
Proof.
  intros K k1 k2 t Hle H. revert K k1 k2 Hle H.
  induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    intros K k1 k2 Hle H; simpl in *; inversion H; subst.
  - constructor; lia.
  - constructor.
  - constructor; [assumption | apply IHb with (k1 := S k1) (k2 := S k2); [lia|assumption]].
  - constructor; [eapply IH1; eassumption | eapply IH2; eassumption].
  - constructor. eapply IHb; eassumption.
  - constructor; [eapply IH1; eassumption | assumption].
  - constructor.
  - constructor. eapply IHb; eassumption.
  - constructor; [eapply IHnn; eassumption | eapply IHbb; eassumption | eapply IHss; eassumption].
Qed.

Lemma lc_ty_open_rec : forall k U T,
  lc_ty_at (S k) T -> lc_ty_at k U -> lc_ty_at k (open_ty_rec k U T).
Proof.
  intros k U T Hlc HU. revert k U Hlc HU.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 | ]; intros k U Hlc HU; simpl.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst; assumption.
    + apply Nat.eqb_neq in E. inversion Hlc; subst. constructor. lia.
  - constructor.
  - inversion Hlc; subst. constructor; eauto.
  - inversion Hlc; subst. constructor.
    eapply IH1; [eassumption | apply lc_ty_at_weaken with (k1:=k); [lia|assumption]].
  - constructor.
Qed.

Lemma lc_ty_open_fvar_inv : forall k X T,
  lc_ty_at k (open_ty_rec k (Ty_FVar X) T) -> lc_ty_at (S k) T.
Proof.
  intros k X T H. revert k X H.
  induction T as [n | Y | T1 IH1 T2 IH2 | T1 IH1 | ]; intros k X H; simpl in H.
  - destruct (Nat.eqb k n) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor. lia.
    + inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; eauto.
  - inversion H; subst. constructor. eapply IH1; eassumption.
  - constructor.
Qed.

Lemma lc_tm_open_rec : forall K k u t,
  lc_tm_at K (S k) t -> lc_tm_at K k u -> lc_tm_at K k (open_tm_rec k u t).
Proof.
  intros K k u t Ht Hu. revert K k u Ht Hu.
  induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    intros K k u Ht Hu; simpl.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst; assumption.
    + apply Nat.eqb_neq in E. inversion Ht; subst. constructor. lia.
  - constructor.
  - inversion Ht; subst. constructor; [assumption | eapply IHb; [eassumption | apply lc_tm_at_weaken_k with (k1:=k); [lia|assumption]]].
  - inversion Ht; subst. constructor; [eapply IH1; eassumption | eapply IH2; eassumption].
  - inversion Ht; subst. constructor. eapply IHb; [eassumption | apply lc_tm_at_weaken_K with (K1:=K); [lia|assumption]].
  - inversion Ht; subst. constructor; [eapply IH1; eassumption | assumption].
  - constructor.
  - inversion Ht; subst. constructor. eapply IHb; eassumption.
  - inversion Ht; subst. constructor; [eapply IHnn; eassumption | eapply IHbb; eassumption | eapply IHss; eassumption].
Qed.

Lemma lc_tm_open_rec_inv : forall K k X t,
  lc_tm_at K k (open_tm_rec k (tm_fvar X) t) -> lc_tm_at K (S k) t.
Proof.
  intros K k X t H. revert K k X H.
  induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    intros K k X H; simpl in H.
  - destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E; subst. constructor. lia.
    + inversion H; subst. constructor. lia.
  - constructor.
  - inversion H; subst. constructor; [assumption | eapply IHb; eassumption].
  - inversion H; subst. constructor; [eapply IH1; eassumption | eapply IH2; eassumption].
  - inversion H; subst. constructor. eapply IHb; eassumption.
  - inversion H; subst. constructor; [eapply IH1; eassumption | assumption].
  - constructor.
  - inversion H; subst. constructor. eapply IHb; eassumption.
  - inversion H; subst. constructor; [eapply IHnn; eassumption | eapply IHbb; eassumption | eapply IHss; eassumption].
Qed.

Lemma lc_tm_open_ty_rec : forall K k U t,
  lc_tm_at (S K) k t -> lc_ty_at K U -> lc_tm_at K k (open_tm_ty_rec K U t).
Proof.
  intros K k U t Ht HU. revert K k U Ht HU.
  induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    intros K k U Ht HU; simpl.
  - inversion Ht; subst. constructor. assumption.
  - constructor.
  - inversion Ht; subst. constructor.
    + eapply lc_ty_open_rec; eassumption.
    + eapply IHb; [eassumption | apply lc_ty_at_weaken with (k1:=K); [lia|assumption]].
  - inversion Ht; subst. constructor; [eapply IH1; eassumption | eapply IH2; eassumption].
  - inversion Ht; subst. constructor.
    eapply IHb; [eassumption | apply lc_ty_at_weaken with (k1:=K); [lia|assumption]].
  - inversion Ht; subst. constructor; [eapply IH1; eassumption | eapply lc_ty_open_rec; eassumption].
  - constructor.
  - inversion Ht; subst. constructor. eapply IHb; eassumption.
  - inversion Ht; subst. constructor; [eapply IHnn; eassumption | eapply IHbb; eassumption | eapply IHss; eassumption].
Qed.

Lemma lc_tm_open_ty_rec_inv : forall K k X t,
  lc_tm_at K k (open_tm_ty_rec K (Ty_FVar X) t) -> lc_tm_at (S K) k t.
Proof.
  intros K k X t H. revert K k X H.
  induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    intros K k X H; simpl in H.
  - apply lc_tm_at_weaken_K with (K1:=K); [lia|assumption].
  - apply lc_tm_at_weaken_K with (K1:=K); [lia|assumption].
  - inversion H; subst. constructor.
    + eapply lc_ty_open_fvar_inv; eassumption.
    + eapply IHb; eassumption.
  - inversion H; subst. constructor; [eapply IH1; eassumption | eapply IH2; eassumption].
  - inversion H; subst. constructor. eapply IHb; eassumption.
  - inversion H; subst. constructor; [eapply IH1; eassumption | eapply lc_ty_open_fvar_inv; eassumption].
  - constructor.
  - inversion H; subst. constructor. eapply IHb; eassumption.
  - inversion H; subst. constructor; [eapply IHnn; eassumption | eapply IHbb; eassumption | eapply IHss; eassumption].
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H as [Delta X Hin | Delta T1 T2 H1 IH1 H2 IH2 | L Delta T Hprem IHprem | Delta].
  - constructor.
  - constructor; assumption.
  - constructor. 
    pose (X := fresh_atom L).
    assert (HX : ~ In X L) by apply fresh_atom_not_in.
    specialize (IHprem X HX).
    eapply lc_ty_open_fvar_inv; eassumption.
  - constructor.
Qed.

Lemma lc_ty_tsubst : forall tau,
  (forall X, lc_ty_at 0 (tau X)) ->
  forall k T, lc_ty_at k T -> lc_ty_at k (tsubst_ty tau T).
Proof.
  intros tau Htau k T Hlc. revert k Hlc.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 | ]; intros k Hlc; simpl; inversion Hlc; subst.
  - constructor; assumption.
  - apply lc_ty_at_weaken with (k1:=0); [lia|apply Htau].
  - constructor; auto.
  - constructor. eapply IH1; eassumption.
  - constructor.
Qed.

Lemma lc_tm_tsubst : forall tau,
  (forall X, lc_ty_at 0 (tau X)) ->
  forall K k t, lc_tm_at K k t -> lc_tm_at K k (tsubst_tm tau t).
Proof.
  intros tau Htau K k t Hlc. revert K k Hlc.
  induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    intros K k Hlc; simpl; inversion Hlc; subst.
  - constructor; assumption.
  - constructor.
  - constructor; [eapply lc_ty_tsubst; eassumption | eapply IHb; eassumption].
  - constructor; auto.
  - constructor. eapply IHb; eassumption.
  - constructor; [eapply IH1; eassumption | eapply lc_ty_tsubst; eassumption].
  - constructor.
  - constructor. eapply IHb; eassumption.
  - constructor; auto.
Qed.

Lemma has_type_lc_ty : forall Delta Gamma t T,
  has_type Delta Gamma t T -> lc_ty_at 0 T.
Proof.
  intros Delta Gamma t T H. induction H.
  - eapply wf_ty_lc; eassumption.
  - constructor.
    + eapply wf_ty_lc; eassumption.
    + match goal with
      | IH : forall x, ~ In x ?L -> lc_ty_at 0 ?T2 |- lc_ty_at 0 ?T2 =>
          pose (xx := fresh_atom L); specialize (IH xx (fresh_atom_not_in L)); exact IH
      end.
  - match goal with
    | IH : lc_ty_at 0 (Ty_Arrow ?T1 ?T2) |- lc_ty_at 0 ?T2 => inversion IH; assumption
    end.
  - constructor.
    match goal with
    | IH : forall x, ~ In x ?L -> lc_ty_at 0 (open_ty ?T (Ty_FVar x)) |- lc_ty_at 1 ?T =>
        pose (xx := fresh_atom L); specialize (IH xx (fresh_atom_not_in L));
        eapply lc_ty_open_fvar_inv; eassumption
    end.
  - match goal with
    | IH : lc_ty_at 0 (Ty_All ?T) |- lc_ty_at 0 (open_ty ?T ?U) =>
        eapply lc_ty_open_rec with (k:=0);
        [inversion IH; assumption | eapply wf_ty_lc; eassumption]
    end.
  - constructor.
  - constructor.
  - assumption.
Qed.

Lemma has_type_lc_tm : forall Delta Gamma t T,
  has_type Delta Gamma t T -> locally_closed_tm t.
Proof.
  intros Delta Gamma t T H. induction H.
  - constructor.
  - constructor.
    + eapply wf_ty_lc; eassumption.
    + match goal with
      | IH : forall x, ~ In x ?L -> locally_closed_tm (open_tm ?body (tm_fvar x))
        |- lc_tm_at 0 1 ?body =>
          pose (xx := fresh_atom L); specialize (IH xx (fresh_atom_not_in L));
          eapply lc_tm_open_rec_inv; eassumption
      end.
  - constructor; assumption.
  - constructor.
    match goal with
    | IH : forall x, ~ In x ?L -> locally_closed_tm (open_tm_ty ?body (Ty_FVar x))
      |- lc_tm_at 1 0 ?body =>
        pose (xx := fresh_atom L); specialize (IH xx (fresh_atom_not_in L));
        eapply lc_tm_open_ty_rec_inv; eassumption
    end.
  - constructor; [assumption | eapply wf_ty_lc; eassumption].
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
Qed.

(* ============================================================ *)
(* Lookup and substitution infrastructure                      *)
(* ============================================================ *)

Lemma lookup_context_update_same : forall x Gamma T,
  lookup_context x (update Gamma x T) = Some T.
Proof.
  intros. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma lookup_context_update_other : forall x y Gamma T,
  x <> y -> lookup_context x (update Gamma y T) = lookup_context x Gamma.
Proof.
  intros x y Gamma T Hneq. simpl.
  destruct (Nat.eqb x y) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. contradiction.
Qed.

Lemma lc_ty_upd_tau : forall tau X U,
  (forall Y, lc_ty_at 0 (tau Y)) -> lc_ty_at 0 U ->
  forall Y, lc_ty_at 0 (upd_tau tau X U Y).
Proof.
  intros tau X U Htau HU Y. unfold upd_tau.
  destruct (Nat.eqb Y X); auto.
Qed.

Lemma lc_env_upd_env : forall sigma x u,
  (forall y, locally_closed_tm (sigma y)) -> locally_closed_tm u ->
  forall y, locally_closed_tm (upd_env sigma x u y).
Proof.
  intros sigma x u Hsig Hu y. unfold upd_env.
  destruct (Nat.eqb y x); auto.
Qed.

Lemma subst_env_ext : forall t sigma tau,
  (forall x, In x (fv_tm t) -> sigma x = tau x) ->
  subst_env sigma t = subst_env tau t.
Proof.
  intros t. induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    intros sigma tau H; simpl.
  - reflexivity.
  - apply H. simpl. auto.
  - f_equal. apply IHb. intros y Hy. apply H. simpl. apply in_or_app. right. assumption.
  - f_equal.
    + apply IH1. intros y Hy. apply H. simpl. apply in_or_app. left. assumption.
    + apply IH2. intros y Hy. apply H. simpl. apply in_or_app. right. assumption.
  - f_equal. apply IHb. intros y Hy. apply H. simpl. assumption.
  - f_equal. apply IH1. intros y Hy. apply H. simpl. apply in_or_app. left. assumption.
  - reflexivity.
  - f_equal. apply IHb. intros y Hy. apply H. simpl. assumption.
  - f_equal.
    + apply IHnn. intros y Hy. apply H. simpl. apply in_or_app. left. assumption.
    + apply IHbb. intros y Hy. apply H. simpl. apply in_or_app. right. apply in_or_app. left. assumption.
    + apply IHss. intros y Hy. apply H. simpl. apply in_or_app. right. apply in_or_app. right. assumption.
Qed.

Lemma subst_env_update_fresh : forall t sigma x u,
  ~ In x (fv_tm t) -> subst_env (upd_env sigma x u) t = subst_env sigma t.
Proof.
  intros t sigma x u Hfresh. apply subst_env_ext.
  intros y Hy. unfold upd_env.
  destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. assumption.
  - reflexivity.
Qed.

Lemma tsubst_ty_ext : forall T tau tau',
  (forall X, In X (fv_ty T) -> tau X = tau' X) ->
  tsubst_ty tau T = tsubst_ty tau' T.
Proof.
  induction T as [n | X | T1 IH1 T2 IH2 | T1 IH1 | ]; intros tau tau' H; simpl.
  - reflexivity.
  - apply H. simpl. auto.
  - f_equal.
    + apply IH1. intros Y HY. apply H. simpl. apply in_or_app. left. assumption.
    + apply IH2. intros Y HY. apply H. simpl. apply in_or_app. right. assumption.
  - f_equal. apply IH1. intros Y HY. apply H. simpl. assumption.
  - reflexivity.
Qed.

Lemma tsubst_tm_ext : forall t tau tau',
  (forall X, In X (fv_tm t) -> tau X = tau' X) ->
  tsubst_tm tau t = tsubst_tm tau' t.
Proof.
  induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    intros tau tau' H; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply tsubst_ty_ext. intros Y HY. apply H. simpl. apply in_or_app. left. assumption.
    + apply IHb. intros Y HY. apply H. simpl. apply in_or_app. right. assumption.
  - f_equal.
    + apply IH1. intros Y HY. apply H. simpl. apply in_or_app. left. assumption.
    + apply IH2. intros Y HY. apply H. simpl. apply in_or_app. right. assumption.
  - f_equal. apply IHb. intros Y HY. apply H. simpl. assumption.
  - f_equal.
    + apply IH1. intros Y HY. apply H. simpl. apply in_or_app. left. assumption.
    + apply tsubst_ty_ext. intros Y HY. apply H. simpl. apply in_or_app. right. assumption.
  - reflexivity.
  - f_equal. apply IHb. intros Y HY. apply H. simpl. assumption.
  - f_equal.
    + apply IHnn. intros Y HY. apply H. simpl. apply in_or_app. left. assumption.
    + apply IHbb. intros Y HY. apply H. simpl. apply in_or_app. right. apply in_or_app. left. assumption.
    + apply IHss. intros Y HY. apply H. simpl. apply in_or_app. right. apply in_or_app. right. assumption.
Qed.

Lemma tsubst_ty_upd_fresh : forall T tau X U,
  ~ In X (fv_ty T) -> tsubst_ty (upd_tau tau X U) T = tsubst_ty tau T.
Proof.
  induction T as [n | Y | T1 IH1 T2 IH2 | T1 IH1 | ]; intros tau X U Hfresh; simpl.
  - reflexivity.
  - unfold upd_tau. destruct (Nat.eqb Y X) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply Hfresh. simpl. auto.
    + reflexivity.
  - f_equal.
    + apply IH1. intros HY. apply Hfresh. simpl. apply in_or_app. left. assumption.
    + apply IH2. intros HY. apply Hfresh. simpl. apply in_or_app. right. assumption.
  - f_equal. apply IH1. intros HY. apply Hfresh. simpl. assumption.
  - reflexivity.
Qed.

Lemma tsubst_tm_upd_fresh : forall t tau X U,
  ~ In X (fv_tm t) -> tsubst_tm (upd_tau tau X U) t = tsubst_tm tau t.
Proof.
  induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    intros tau X U Hfresh; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal.
    + apply tsubst_ty_upd_fresh. intros HY. apply Hfresh. simpl. apply in_or_app. left. assumption.
    + apply IHb. intros HY. apply Hfresh. simpl. apply in_or_app. right. assumption.
  - f_equal.
    + apply IH1. intros HY. apply Hfresh. simpl. apply in_or_app. left. assumption.
    + apply IH2. intros HY. apply Hfresh. simpl. apply in_or_app. right. assumption.
  - f_equal. apply IHb. intros HY. apply Hfresh. simpl. assumption.
  - f_equal.
    + apply IH1. intros HY. apply Hfresh. simpl. apply in_or_app. left. assumption.
    + apply tsubst_ty_upd_fresh. intros HY. apply Hfresh. simpl. apply in_or_app. right. assumption.
  - reflexivity.
  - f_equal. apply IHb. intros HY. apply Hfresh. simpl. assumption.
  - f_equal.
    + apply IHnn. intros HY. apply Hfresh. simpl. apply in_or_app. left. assumption.
    + apply IHbb. intros HY. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. left. assumption.
    + apply IHss. intros HY. apply Hfresh. simpl. apply in_or_app. right. apply in_or_app. right. assumption.
Qed.

Lemma tsubst_ty_open_ty : forall tau T U,
  (forall X, lc_ty_at 0 (tau X)) ->
  tsubst_ty tau (open_ty T U) = open_ty (tsubst_ty tau T) (tsubst_ty tau U).
Proof.
  intros. unfold open_ty. erewrite tsubst_ty_open_ty_rec; [reflexivity | assumption].
Qed.

Lemma tsubst_ty_open_fvar : forall tau X Y T,
  (forall Z, lc_ty_at 0 (tau Z)) ->
  ~ In X (fv_ty T) ->
  tsubst_ty (upd_tau tau X (Ty_FVar Y)) (open_ty T (Ty_FVar X))
  = open_ty (tsubst_ty tau T) (Ty_FVar Y).
Proof.
  intros tau X Y T Htau Hfresh. unfold open_ty.
  erewrite tsubst_ty_open_ty_rec;
    [| apply lc_ty_upd_tau; [assumption | constructor]].
  rewrite (tsubst_ty_upd_fresh T tau X (Ty_FVar Y) Hfresh).
  replace (tsubst_ty (upd_tau tau X (Ty_FVar Y)) (Ty_FVar X)) with (Ty_FVar Y).
  - reflexivity.
  - cbn [tsubst_ty]. unfold upd_tau. cbn [Nat.eqb]. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma tsubst_tm_open_fvar : forall tau X Y body,
  (forall Z, lc_ty_at 0 (tau Z)) ->
  ~ In X (fv_tm body) ->
  tsubst_tm (upd_tau tau X (Ty_FVar Y)) (open_tm_ty body (Ty_FVar X))
  = open_tm_ty (tsubst_tm tau body) (Ty_FVar Y).
Proof.
  intros tau X Y body Htau Hfresh. unfold open_tm_ty.
  erewrite tsubst_tm_open_tm_ty_rec;
    [| apply lc_ty_upd_tau; [assumption | constructor]].
  rewrite (tsubst_tm_upd_fresh body tau X (Ty_FVar Y) Hfresh).
  replace (tsubst_ty (upd_tau tau X (Ty_FVar Y)) (Ty_FVar X)) with (Ty_FVar Y).
  - reflexivity.
  - cbn [tsubst_ty]. unfold upd_tau. cbn [Nat.eqb]. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma subst_env_upd_env_open : forall sigma x u body,
  (forall y, locally_closed_tm (sigma y)) ->
  locally_closed_tm u ->
  ~ In x (fv_tm body) ->
  subst_env (upd_env sigma x u) (open_tm body (tm_fvar x))
  = open_tm (subst_env sigma body) u.
Proof.
  intros sigma x u body Hsig Hu Hfresh. unfold open_tm.
  rewrite subst_env_open_tm_rec.
  - rewrite (subst_env_update_fresh body sigma x u Hfresh).
    cbn [subst_env]. unfold upd_env. cbn [Nat.eqb]. rewrite Nat.eqb_refl. reflexivity.
  - apply lc_env_upd_env; assumption.
Qed.

Lemma subst_env_open_tm_ty_fvar : forall sigma body X,
  (forall y, locally_closed_tm (sigma y)) ->
  subst_env sigma (open_tm_ty body (Ty_FVar X))
  = open_tm_ty (subst_env sigma body) (Ty_FVar X).
Proof.
  intros. unfold open_tm_ty. erewrite subst_env_open_tm_ty_rec; [reflexivity | assumption].
Qed.

(* ============================================================ *)
(* Values, numeric values, and canonicalization                 *)
(* ============================================================ *)

Lemma numeric_value_lc : forall n, numeric_value n -> locally_closed_tm n.
Proof.
  intros n H. induction H.
  - constructor.
  - constructor. assumption.
Qed.

Lemma numeric_value_value : forall n, numeric_value n -> value n.
Proof. intros. constructor. assumption. Qed.

Lemma numeric_value_no_step : forall n, numeric_value n -> forall u, ~ step n u.
Proof.
  intros n H. induction H; intros u Hstep; inversion Hstep; subst;
    try match goal with
    | IH : forall w, ~ ?a --> w, Hs : ?a --> ?b |- False => exact (IH b Hs)
    end.
Qed.

Lemma numeric_value_sn : forall n, numeric_value n -> strongly_normalizing n.
Proof.
  intros n H. apply SN_intro. intros u Hstep.
  exfalso. eapply numeric_value_no_step; eassumption.
Qed.

Lemma numeric_value_multi : forall n u, numeric_value n -> multi n u -> u = n.
Proof.
  intros n u H Hm. destruct Hm as [x | x y z Hstep Hm].
  - reflexivity.
  - exfalso. eapply numeric_value_no_step; eassumption.
Qed.

Lemma value_lc : forall v, value v -> locally_closed_tm v.
Proof.
  intros v H. induction H.
  - assumption.
  - assumption.
  - apply numeric_value_lc. assumption.
Qed.

Lemma value_no_step : forall v u, value v -> ~ step v u.
Proof.
  intros v u H. induction H.
  - intros Hstep. inversion Hstep.
  - intros Hstep. inversion Hstep.
  - apply numeric_value_no_step. assumption.
Qed.

Lemma value_multi : forall v u, value v -> multi v u -> u = v.
Proof.
  intros v u H Hm. destruct Hm as [x | x y z Hstep Hm].
  - reflexivity.
  - exfalso. eapply value_no_step; eassumption.
Qed.

Lemma lc_canon : forall K k t, lc_tm_at K k t -> lc_tm_at K k (canon t).
Proof.
  intros K k t H. revert K k H.
  induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    intros K k Hlc; simpl; inversion Hlc; subst; eauto.
Qed.

Lemma canon_numeric : forall n, numeric_value n -> numeric_value (canon n).
Proof.
  intros n H. induction H.
  - simpl. constructor.
  - simpl. constructor. assumption.
Qed.

Lemma canon_numeric_reflect : forall n, numeric_value (canon n) -> numeric_value n.
Proof.
  intros n H.
  induction n as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    simpl in H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - inversion H.
  - exact nv_zero.
  - inversion H; subst. apply nv_succ. apply IHb. assumption.
  - inversion H.
Qed.

Lemma canon_value : forall v, value v -> value (canon v).
Proof.
  intros v H. induction H.
  - simpl. apply v_abs. constructor.
    + constructor.
    + inversion H; subst. apply lc_canon. assumption.
  - simpl. apply v_tabs. constructor. inversion H; subst. apply lc_canon. assumption.
  - simpl. apply numeric_value_value. apply canon_numeric. assumption.
Qed.

Lemma canon_value_reflect : forall t, locally_closed_tm t -> value (canon t) -> value t.
Proof.
  intros t Hlc Hv. destruct t; simpl in Hv.
  - inversion Hv; subst; match goal with Hn : numeric_value _ |- _ => inversion Hn end.
  - inversion Hv; subst; match goal with Hn : numeric_value _ |- _ => inversion Hn end.
  - apply v_abs. exact Hlc.
  - inversion Hv; subst; match goal with Hn : numeric_value _ |- _ => inversion Hn end.
  - apply v_tabs. exact Hlc.
  - inversion Hv; subst; match goal with Hn : numeric_value _ |- _ => inversion Hn end.
  - apply v_nat. constructor.
  - inversion Hv; subst.
    match goal with Hn : numeric_value (tm_succ (canon t)) |- _ => inversion Hn; subst end.
    apply v_nat. constructor. apply canon_numeric_reflect. assumption.
  - inversion Hv; subst; match goal with Hn : numeric_value _ |- _ => inversion Hn end.
Qed.

Lemma canon_open_tm : forall k u t,
  canon (open_tm_rec k u t) = open_tm_rec k (canon u) (canon t).
Proof.
  intros k u t. revert k u.
  induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    intros k u; simpl.
  - destruct (Nat.eqb k i); reflexivity.
  - reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite IH1. reflexivity.
  - reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite IHnn, IHbb, IHss. reflexivity.
Qed.

Lemma canon_open_tm_ty : forall K U t,
  canon (open_tm_ty_rec K U t) = open_tm_ty_rec K Ty_Nat (canon t).
Proof.
  intros K U t. revert K U.
  induction t as [i | x | T b IHb | t1 IH1 t2 IH2 | b IHb | t1 IH1 T | | t IHb | nn IHnn bb IHbb ss IHss];
    intros K U; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite IH1. reflexivity.
  - reflexivity.
  - rewrite IHb. reflexivity.
  - rewrite IHnn, IHbb, IHss. reflexivity.
Qed.

Ltac use_ih :=
  match goal with
  | IH : locally_closed_tm ?a -> locally_closed_tm ?b, Ha : lc_tm_at 0 0 ?a
    |- lc_tm_at 0 0 ?b => apply IH; exact Ha
  end.

Lemma step_lc : forall t u, step t u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u H. induction H; intros Hlc; simpl in Hlc; inversion Hlc; subst.
  - (* AppAbs *)
    match goal with
    | Habs : lc_tm_at 0 0 (tm_abs ?T ?body), Hv : lc_tm_at 0 0 ?v
      |- locally_closed_tm (open_tm ?body ?v) =>
        unfold open_tm; eapply lc_tm_open_rec; [inversion Habs; assumption | exact Hv]
    end.
  - (* App1 *) apply lc_tm_app; [use_ih | assumption].
  - (* App2 *) apply lc_tm_app; [assumption | use_ih].
  - (* TAppTabs *)
    match goal with
    | Habs : lc_tm_at 0 0 (tm_tabs ?body), HT : lc_ty_at 0 ?T
      |- locally_closed_tm (open_tm_ty ?body ?T) =>
        unfold open_tm_ty; eapply lc_tm_open_ty_rec; [inversion Habs; assumption | exact HT]
    end.
  - (* TApp *) apply lc_tm_tapp; [use_ih | assumption].
  - (* Succ *) apply lc_tm_succ; use_ih.
  - (* RecArg *) apply lc_tm_rec; [use_ih | assumption | assumption].
  - (* RecBase *) apply lc_tm_rec; [assumption | use_ih | assumption].
  - (* RecStep *) apply lc_tm_rec; [assumption | assumption | use_ih].
  - (* RecZero *) assumption.
  - (* RecSucc *) apply lc_tm_app.
    + apply lc_tm_app.
      * assumption.
      * apply numeric_value_lc. assumption.
    + apply lc_tm_rec.
      * apply numeric_value_lc. assumption.
      * assumption.
      * assumption.
Qed.
Arguments step_lc {t} {u} _ _.


Lemma canon_step_sim : forall t u, step t u -> locally_closed_tm t -> step (canon t) (canon u).
Proof.
  intros t u H. induction H; intros Hlc; simpl in *; inversion Hlc; subst.
  - (* AppAbs *)
    unfold open_tm. erewrite canon_open_tm.
    eapply ST_AppAbs.
    + constructor. constructor. inversion H; subst. apply lc_canon. assumption.
    + apply canon_value. assumption.
  - (* App1 *)
    eapply ST_App1.
    + apply IHstep. assumption.
    + apply lc_canon. assumption.
  - (* App2 *)
    eapply ST_App2.
    + apply canon_value. assumption.
    + apply IHstep. assumption.
  - (* TAppTabs *)
    unfold open_tm_ty. erewrite canon_open_tm_ty.
    eapply ST_TAppTabs.
    + constructor. inversion H; subst. apply lc_canon. assumption.
    + constructor.
  - (* TApp *)
    eapply ST_TApp.
    + apply IHstep. assumption.
    + constructor.
  - (* Succ *)
    apply ST_Succ. apply IHstep. assumption.
  - (* RecArg *)
    eapply ST_RecArg.
    + apply IHstep. assumption.
    + apply lc_canon. assumption.
    + apply lc_canon. assumption.
  - (* RecBase *)
    eapply ST_RecBase.
    + apply canon_numeric. assumption.
    + apply IHstep. assumption.
    + apply lc_canon. assumption.
  - (* RecStep *)
    eapply ST_RecStep.
    + apply canon_numeric. assumption.
    + apply canon_value. assumption.
    + apply IHstep. assumption.
  - (* RecZero *)
    eapply ST_RecZero.
    + apply canon_value. assumption.
    + apply canon_value. assumption.
  - (* RecSucc *)
    eapply ST_RecSucc.
    + apply canon_numeric. assumption.
    + apply canon_value. assumption.
    + apply canon_value. assumption.
Qed.
Arguments canon_step_sim {t} {u} _ _.


Lemma canon_abs_inv : forall t T b, canon t = tm_abs T b ->
  exists T0 b0, t = tm_abs T0 b0 /\ T = Ty_Nat /\ canon b0 = b.
Proof.
  intros t T b H. destruct t; simpl in H; try discriminate.
  inversion H; subst. eexists; eexists; repeat split; eauto.
Qed.

Lemma canon_app_inv : forall t a b, canon t = tm_app a b ->
  exists t1 t2, t = tm_app t1 t2 /\ canon t1 = a /\ canon t2 = b.
Proof.
  intros t a b H. destruct t; simpl in H; try discriminate.
  inversion H; subst. eexists; eexists; repeat split; eauto.
Qed.

Lemma canon_tabs_inv : forall t b, canon t = tm_tabs b ->
  exists b0, t = tm_tabs b0 /\ canon b0 = b.
Proof.
  intros t b H. destruct t; simpl in H; try discriminate.
  inversion H; subst. eexists; repeat split; eauto.
Qed.

Lemma canon_tapp_inv : forall t a T, canon t = tm_tapp a T ->
  exists t1 T0, t = tm_tapp t1 T0 /\ canon t1 = a /\ T = Ty_Nat.
Proof.
  intros t a T H. destruct t; simpl in H; try discriminate.
  inversion H; subst. eexists; eexists; repeat split; eauto.
Qed.

Lemma canon_zero_inv : forall t, canon t = tm_zero -> t = tm_zero.
Proof.
  intros t H. destruct t; simpl in H; try discriminate; reflexivity.
Qed.

Lemma canon_succ_inv : forall t n, canon t = tm_succ n ->
  exists t0, t = tm_succ t0 /\ canon t0 = n.
Proof.
  intros t n H. destruct t; simpl in H; try discriminate.
  inversion H; subst. eexists; repeat split; eauto.
Qed.

Lemma canon_natrec_inv : forall t a b c, canon t = tm_natrec a b c ->
  exists n1 b1 s1, t = tm_natrec n1 b1 s1 /\
    canon n1 = a /\ canon b1 = b /\ canon s1 = c.
Proof.
  intros t a b c H. destruct t; simpl in H; try discriminate.
  inversion H; subst. eexists; eexists; eexists; repeat split; eauto.
Qed.

Lemma lc_app_inv : forall K k t1 t2,
  lc_tm_at K k (tm_app t1 t2) -> lc_tm_at K k t1 /\ lc_tm_at K k t2.
Proof. intros. inversion H; subst; split; assumption. Qed.

Lemma lc_abs_inv : forall K k T b,
  lc_tm_at K k (tm_abs T b) -> lc_ty_at K T /\ lc_tm_at K (S k) b.
Proof. intros. inversion H; subst; split; assumption. Qed.

Lemma lc_tapp_inv : forall K k t T,
  lc_tm_at K k (tm_tapp t T) -> lc_tm_at K k t /\ lc_ty_at K T.
Proof. intros. inversion H; subst; split; assumption. Qed.

Lemma lc_succ_inv : forall K k t,
  lc_tm_at K k (tm_succ t) -> lc_tm_at K k t.
Proof. intros. inversion H; subst; assumption. Qed.

Lemma lc_rec_inv : forall K k n b s,
  lc_tm_at K k (tm_natrec n b s) ->
  lc_tm_at K k n /\ lc_tm_at K k b /\ lc_tm_at K k s.
Proof. intros. inversion H; subst; repeat split; assumption. Qed.

Lemma canon_step_lift : forall t u, step (canon t) u -> locally_closed_tm t ->
  exists u0, step t u0 /\ canon u0 = u.
Proof.
  assert (Hgen : forall x y, step x y ->
    forall tt, canon tt = x -> locally_closed_tm tt ->
      exists u0, step tt u0 /\ canon u0 = y).
  { intros x y Hstep tt Hcanon Hlc. revert tt Hcanon Hlc.
    induction Hstep; intros tt Hcanon Hlc.
    - (* AppAbs *)
      apply canon_app_inv in Hcanon.
      destruct Hcanon as [u1 [u2 [Heq [Hc1 Hc2]]]]. subst tt.
      apply canon_abs_inv in Hc1.
      destruct Hc1 as [T0 [b0 [Heq1 [HT Hcb]]]]. subst u1. subst T.
      destruct (lc_app_inv _ _ _ _ Hlc) as [Hla Hlb].
      assert (Hvu2 : value u2).
      { apply canon_value_reflect; [exact Hlb | rewrite Hc2; exact H0]. }
      exists (open_tm b0 u2). split.
      + eapply ST_AppAbs; [exact Hla | exact Hvu2].
      + unfold open_tm. rewrite canon_open_tm. rewrite Hcb, Hc2. reflexivity.
    - (* App1 *)
      apply canon_app_inv in Hcanon.
      destruct Hcanon as [u1 [u2 [Heq [Hc1 Hc2]]]]. subst tt.
      destruct (lc_app_inv _ _ _ _ Hlc) as [Hla Hlb].
      specialize (IHHstep u1 Hc1 Hla).
      destruct IHHstep as [u1' [Hstep1 Hcanon1]].
      exists (tm_app u1' u2). split.
      + eapply ST_App1; [exact Hstep1 | exact Hlb].
      + simpl. rewrite Hcanon1, Hc2. reflexivity.
    - (* App2 *)
      apply canon_app_inv in Hcanon.
      destruct Hcanon as [u1 [u2 [Heq [Hc1 Hc2]]]]. subst tt.
      destruct (lc_app_inv _ _ _ _ Hlc) as [Hla Hlb].
      assert (Hvu1 : value u1).
      { apply canon_value_reflect; [exact Hla | rewrite Hc1; exact H]. }
      specialize (IHHstep u2 Hc2 Hlb).
      destruct IHHstep as [u2' [Hstep2 Hcanon2]].
      exists (tm_app u1 u2'). split.
      + eapply ST_App2; eassumption.
      + simpl. rewrite Hc1, Hcanon2. reflexivity.
    - (* TAppTabs *)
      apply canon_tapp_inv in Hcanon.
      destruct Hcanon as [u1 [T0 [Heq [Hc1 HT]]]]. subst tt.
      apply canon_tabs_inv in Hc1.
      destruct Hc1 as [b0 [Heq1 Hcb]]; subst u1.
      destruct (lc_tapp_inv _ _ _ _ Hlc) as [Hla HlT].
      exists (open_tm_ty b0 T0). split.
      + eapply ST_TAppTabs; [exact Hla | exact HlT].
      + unfold open_tm_ty. rewrite canon_open_tm_ty.
        rewrite Hcb. rewrite <- HT. reflexivity.
    - (* TApp *)
      apply canon_tapp_inv in Hcanon.
      destruct Hcanon as [u1 [T0 [Heq [Hc1 HT]]]]. subst tt.
      destruct (lc_tapp_inv _ _ _ _ Hlc) as [Hla HlT].
      specialize (IHHstep u1 Hc1 Hla).
      destruct IHHstep as [u1' [Hstep1 Hcanon1]].
      exists (tm_tapp u1' T0). split.
      + eapply ST_TApp; [exact Hstep1 | exact HlT].
      + simpl. rewrite Hcanon1. rewrite <- HT. reflexivity.
    - (* Succ *)
      apply canon_succ_inv in Hcanon.
      destruct Hcanon as [u1 [Heq Hc1]]; subst tt.
      pose proof (lc_succ_inv _ _ _ Hlc) as Hla.
      specialize (IHHstep u1 Hc1 Hla).
      destruct IHHstep as [u1' [Hstep1 Hcanon1]].
      exists (tm_succ u1'). split.
      + apply ST_Succ; assumption.
      + simpl. rewrite Hcanon1. reflexivity.
    - (* RecArg *)
      apply canon_natrec_inv in Hcanon.
      destruct Hcanon as [u1 [u2 [u3 [Heq [Hc1 [Hc2 Hc3]]]]]]. subst tt.
      destruct (lc_rec_inv _ _ _ _ _ Hlc) as [Hla [Hlb Hlc3]].
      specialize (IHHstep u1 Hc1 Hla).
      destruct IHHstep as [u1' [Hstep1 Hcanon1]].
      exists (tm_natrec u1' u2 u3). split.
      + eapply ST_RecArg; [exact Hstep1 | exact Hlb | exact Hlc3].
      + simpl. rewrite Hcanon1, Hc2, Hc3. reflexivity.
    - (* RecBase *)
      apply canon_natrec_inv in Hcanon.
      destruct Hcanon as [u1 [u2 [u3 [Heq [Hc1 [Hc2 Hc3]]]]]]. subst tt.
      destruct (lc_rec_inv _ _ _ _ _ Hlc) as [Hla [Hlb Hlc3]].
      assert (Hnum' : numeric_value u1).
      { apply canon_numeric_reflect. rewrite Hc1. exact H. }
      specialize (IHHstep u2 Hc2 Hlb).
      destruct IHHstep as [u2' [Hstep2 Hcanon2]].
      exists (tm_natrec u1 u2' u3). split.
      + eapply ST_RecBase; [exact Hnum' | exact Hstep2 | exact Hlc3].
      + simpl. rewrite Hc1, Hcanon2, Hc3. reflexivity.
    - (* RecStep *)
      apply canon_natrec_inv in Hcanon.
      destruct Hcanon as [u1 [u2 [u3 [Heq [Hc1 [Hc2 Hc3]]]]]]. subst tt.
      destruct (lc_rec_inv _ _ _ _ _ Hlc) as [Hla [Hlb Hlc3]].
      assert (Hnum' : numeric_value u1).
      { apply canon_numeric_reflect. rewrite Hc1. exact H. }
      assert (Hv' : value u2).
      { apply canon_value_reflect; [exact Hlb | rewrite Hc2; exact H0]. }
      specialize (IHHstep u3 Hc3 Hlc3).
      destruct IHHstep as [u3' [Hstep3 Hcanon3]].
      exists (tm_natrec u1 u2 u3'). split.
      + eapply ST_RecStep; eassumption.
      + simpl. rewrite Hc1, Hc2, Hcanon3. reflexivity.
    - (* RecZero *)
      apply canon_natrec_inv in Hcanon.
      destruct Hcanon as [u1 [u2 [u3 [Heq [Hc1 [Hc2 Hc3]]]]]]. subst tt.
      apply canon_zero_inv in Hc1. subst u1.
      destruct (lc_rec_inv _ _ _ _ _ Hlc) as [Hla [Hlb Hlc3]].
      assert (Hv' : value u2).
      { apply canon_value_reflect; [exact Hlb | rewrite Hc2; exact H]. }
      assert (Hw' : value u3).
      { apply canon_value_reflect; [exact Hlc3 | rewrite Hc3; exact H0]. }
      exists u2. split.
      + apply ST_RecZero; assumption.
      + exact Hc2.
    - (* RecSucc *)
      apply canon_natrec_inv in Hcanon.
      destruct Hcanon as [u1 [u2 [u3 [Heq [Hc1 [Hc2 Hc3]]]]]]. subst tt.
      apply canon_succ_inv in Hc1.
      destruct Hc1 as [u0 [Heq1 Hc0]]; subst u1.
      destruct (lc_rec_inv _ _ _ _ _ Hlc) as [Hla [Hlb Hlc3]].
      assert (Hnum' : numeric_value u0).
      { apply canon_numeric_reflect. rewrite Hc0. exact H. }
      assert (Hv' : value u2).
      { apply canon_value_reflect; [exact Hlb | rewrite Hc2; exact H0]. }
      assert (Hw' : value u3).
      { apply canon_value_reflect; [exact Hlc3 | rewrite Hc3; exact H1]. }
      exists (tm_app (tm_app u3 u0) (tm_natrec u0 u2 u3)). split.
      + eapply ST_RecSucc; eassumption.
      + simpl. rewrite Hc3, Hc0, Hc2. reflexivity.
  }
  intros. eapply Hgen; [exact H | reflexivity | exact H0].
Qed.
Arguments canon_step_lift {t} {u} _ _.

(* ============================================================ *)
(* Multi-step correspondence and SN under canonicalization      *)
(* ============================================================ *)

Lemma multi_lc : forall t u, multi t u -> locally_closed_tm t -> locally_closed_tm u.
Proof.
  intros t u H. induction H as [x | x y z Hstep Hm IHm]; intros Hlc.
  - exact Hlc.
  - apply IHm. eapply step_lc; eassumption.
Qed.
Arguments multi_lc {t} {u} _ _.


Lemma multi_canon_sim : forall t u, multi t u -> locally_closed_tm t ->
  multi (canon t) (canon u).
Proof.
  intros t u H. induction H as [x | x y z Hstep Hm IHm]; intros Hlc.
  - apply multi_refl.
  - apply multi_step with (y := canon y).
    + eapply canon_step_sim; eassumption.
    + apply IHm. eapply step_lc; eassumption.
Qed.
Arguments multi_canon_sim {t} {u} _ _.


Lemma multi_canon_lift_gen : forall x u, multi x u ->
  forall t, canon t = x -> locally_closed_tm t ->
    exists u0, multi t u0 /\ canon u0 = u.
Proof.
  intros x u Hm. induction Hm as [x0 | x0 y z Hstep Hm IHm]; intros t Hcanon Hlc.
  - exists t. split; [apply multi_refl | exact Hcanon].
  - assert (Hstep' : step (canon t) y) by (rewrite Hcanon; exact Hstep).
    destruct (canon_step_lift Hstep' Hlc) as [t1 [Hstep1 Hcanon1]].
    destruct (IHm t1 Hcanon1 (step_lc Hstep1 Hlc)) as [t2 [Hm2 Hcanon2]].
    exists t2. split; [| exact Hcanon2].
    eapply multi_step; eassumption.
Qed.

Lemma multi_canon_lift : forall t u, locally_closed_tm t -> multi (canon t) u ->
  exists u0, multi t u0 /\ canon u0 = u.
Proof.
  intros. eapply multi_canon_lift_gen; [exact H0 | reflexivity | exact H].
Qed.
Arguments multi_canon_lift {t} {u} _ _.


Lemma SN_canon_forward : forall t,
  locally_closed_tm t -> strongly_normalizing t -> strongly_normalizing (canon t).
Proof.
  intros t Hlc Hsn. revert Hlc.
  induction Hsn as [t0 Hsteps IHs]. intros Hlc.
  apply SN_intro. intros u Hu.
  destruct (canon_step_lift Hu Hlc) as [t1 [Hstep1 Hcanon1]].
  rewrite <- Hcanon1.
  apply IHs; [exact Hstep1 | eapply step_lc; eassumption].
Qed.

Lemma SN_canon_backward_gen : forall c, strongly_normalizing c ->
  forall t, canon t = c -> locally_closed_tm t -> strongly_normalizing t.
Proof.
  intros c Hsn. induction Hsn as [c0 Hsteps IHs]. intros t Hcanon Hlc.
  apply SN_intro. intros u Hu.
  assert (Hstepc : step c0 (canon u)).
  { rewrite <- Hcanon. apply canon_step_sim; assumption. }
  apply (IHs _ Hstepc u eq_refl). eapply step_lc; eassumption.
Qed.

Lemma SN_canon_backward : forall t,
  locally_closed_tm t -> strongly_normalizing (canon t) -> strongly_normalizing t.
Proof.
  intros. eapply SN_canon_backward_gen; [exact H0 | reflexivity | exact H].
Qed.
Arguments SN_canon_forward {t} _ _.
Arguments SN_canon_backward {t} _ _.


Lemma SN_canon_iff : forall t,
  locally_closed_tm t -> (strongly_normalizing t <-> strongly_normalizing (canon t)).
Proof.
  intros. split; [apply SN_canon_forward | apply SN_canon_backward]; assumption.
Qed.

(* ============================================================ *)
(* Reducibility candidates                                      *)
(* ============================================================ *)

Record cand := {
  cpred : tm -> Prop;
  c_lc : forall t, cpred t -> locally_closed_tm t;
  c_sn : forall t, cpred t -> strongly_normalizing t;
  c_step : forall t u, cpred t -> step t u -> cpred u;
  c_expand : forall t, locally_closed_tm t -> ~ value t ->
      (forall u, step t u -> cpred u) -> cpred t;
  c_inv : forall t t', locally_closed_tm t -> locally_closed_tm t' ->
      canon t = canon t' -> cpred t -> cpred t'
}.

Definition mk_cand (V : tm -> Prop)
  (Vinv : forall v v', locally_closed_tm v -> locally_closed_tm v' ->
      canon v = canon v' -> V v -> V v') : cand.
Proof.
  refine {| cpred t := locally_closed_tm t /\ strongly_normalizing t /\
                        (forall v, multi t v -> value v -> V v) |}.
  - intros t H. exact (proj1 H).
  - intros t H. exact (proj1 (proj2 H)).
  - intros t u H Hstep. destruct H as [Hlc [Hsn HV]]. split; [|split].
    + eapply step_lc; eassumption.
    + destruct Hsn as [t0 HstepSN]. apply HstepSN. exact Hstep.
    + intros v Hm Hval. apply HV with (v := v).
      * eapply multi_step; eassumption.
      * exact Hval.
  - intros t Hlc Hnv Hall. split; [exact Hlc | split].
    + apply SN_intro. intros u Hu.
      exact (proj1 (proj2 (Hall u Hu))).
    + intros v Hm Hval. destruct Hm as [x | x y z Hstep Hm].
      * exfalso. apply Hnv. exact Hval.
      * apply (proj2 (proj2 (Hall y Hstep)) z Hm Hval).
  - intros t t' Hlc Hlc' Hcanon H. destruct H as [Hlc0 [Hsn HV]].
    split; [exact Hlc' | split].
    + pose proof (SN_canon_forward Hlc Hsn) as Hsc.
      rewrite Hcanon in Hsc.
      apply (SN_canon_backward Hlc' Hsc).
    + intros v Hm Hval.
      assert (Hm' : multi (canon t) (canon v)).
      { rewrite Hcanon. apply multi_canon_sim; assumption. }
      destruct (multi_canon_lift Hlc Hm') as [v0 [Hm0 Hcanon0]].
      assert (Hval0 : value v0).
      { apply canon_value_reflect.
        - eapply multi_lc; eassumption.
        - rewrite Hcanon0. apply canon_value. exact Hval. }
      assert (HV0 : V v0).
      { apply HV; assumption. }
      apply (Vinv v0 v).
      * eapply multi_lc; eassumption.
      * apply value_lc. exact Hval.
      * exact Hcanon0.
      * exact HV0.
Defined.

Definition nat_cand : cand.
Proof.
  apply (mk_cand numeric_value).
  intros v v' Hlc Hlc' Hc Hnum.
  apply canon_numeric_reflect.
  rewrite <- Hc.
  apply canon_numeric. exact Hnum.
Defined.

Definition arrow_V (A B : cand) (v : tm) : Prop :=
  forall u, cpred A u -> value u -> cpred B (tm_app v u).

Definition arrow_cand (A B : cand) : cand.
Proof.
  apply (mk_cand (arrow_V A B)).
  intros v v' Hlc Hlc' Hc HV u Hu Hvu.
  apply (c_inv B (tm_app v u) (tm_app v' u)).
  - apply (c_lc B). apply HV; assumption.
  - apply lc_tm_app.
    + exact Hlc'.
    + apply (c_lc A). exact Hu.
  - simpl. rewrite Hc. reflexivity.
  - apply HV; assumption.
Defined.

Definition cons_cand (C : cand) (env : nat -> cand) : nat -> cand :=
  fun i => match i with O => C | S j => env j end.

Lemma canon_tapp_nat : forall v v', canon v = canon v' ->
  canon (tm_tapp v Ty_Nat) = canon (tm_tapp v' Ty_Nat).
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Fixpoint interp (rho : atom -> cand) (env : nat -> cand) (T : ty) : cand :=
  match T with
  | Ty_BVar i => env i
  | Ty_FVar X => rho X
  | Ty_Nat => nat_cand
  | Ty_Arrow T1 T2 => arrow_cand (interp rho env T1) (interp rho env T2)
  | Ty_All T1 =>
      mk_cand
        (fun v => forall C : cand,
            cpred (interp rho (cons_cand C env) T1) (tm_tapp v Ty_Nat))
        (fun v v' Hlc Hlc' Hcanon HV C =>
            c_inv (interp rho (cons_cand C env) T1)
              (tm_tapp v Ty_Nat) (tm_tapp v' Ty_Nat)
              (lc_tm_tapp 0 0 v Ty_Nat Hlc (lc_ty_nat 0))
              (lc_tm_tapp 0 0 v' Ty_Nat Hlc' (lc_ty_nat 0))
              (canon_tapp_nat v v' Hcanon)
              (HV C))
  end.
(* ============================================================ *)
(* Equivalence of candidate interpretations                     *)
(* ============================================================ *)

Lemma mk_cand_pred : forall (V : tm -> Prop) Vi t,
  cpred (mk_cand V Vi) t <->
  locally_closed_tm t /\ strongly_normalizing t /\
    (forall v, multi t v -> value v -> V v).
Proof.
  intros. unfold mk_cand. simpl. tauto.
Qed.

Lemma arrow_cand_pred : forall A B t,
  cpred (arrow_cand A B) t <->
  locally_closed_tm t /\ strongly_normalizing t /\
    (forall v, multi t v -> value v ->
       forall u, cpred A u -> value u -> cpred B (tm_app v u)).
Proof.
  intros. unfold arrow_cand, arrow_V. rewrite mk_cand_pred. tauto.
Qed.

Definition cand_equiv (A B : cand) : Prop := forall t, cpred A t <-> cpred B t.

Lemma cand_equiv_refl : forall A, cand_equiv A A.
Proof. intros A t; tauto. Qed.

Lemma cand_equiv_trans : forall A B C,
  cand_equiv A B -> cand_equiv B C -> cand_equiv A C.
Proof.
  intros A B C H1 H2 t. split; intros H.
  - apply (proj1 (H2 t)). apply (proj1 (H1 t)). exact H.
  - apply (proj2 (H1 t)). apply (proj2 (H2 t)). exact H.
Qed.

Lemma mk_cand_equiv : forall (V W : tm -> Prop) Vi Wi,
  (forall v, V v <-> W v) -> cand_equiv (mk_cand V Vi) (mk_cand W Wi).
Proof.
  intros V W Vi Wi H t. rewrite !mk_cand_pred.
  split.
  - intros [H1 [H2 H3]]. split; [exact H1 | split; [exact H2 |]].
    intros v Hm Hval. apply H. apply H3; assumption.
  - intros [H1 [H2 H3]]. split; [exact H1 | split; [exact H2 |]].
    intros v Hm Hval. apply H. apply H3; assumption.
Qed.

Lemma arrow_cand_equiv : forall A A' B B',
  cand_equiv A A' -> cand_equiv B B' ->
  cand_equiv (arrow_cand A B) (arrow_cand A' B').
Proof.
  intros A A' B B' HA HB t.
  rewrite !arrow_cand_pred.
  split.
  - intros [H1 [H2 H3]]. split; [exact H1 | split; [exact H2 |]].
    intros v Hm Hval u Hu Hvu.
    apply (proj1 (HB (tm_app v u))).
    apply (H3 v Hm Hval u).
    * apply (proj2 (HA u)). exact Hu.
    * exact Hvu.
  - intros [H1 [H2 H3]]. split; [exact H1 | split; [exact H2 |]].
    intros v Hm Hval u Hu Hvu.
    apply (proj2 (HB (tm_app v u))).
    apply (H3 v Hm Hval u).
    * apply (proj1 (HA u)). exact Hu.
    * exact Hvu.
Qed.

Lemma all_cand_equiv : forall (F F' : cand -> cand) Vi Vi',
  (forall C, cand_equiv (F C) (F' C)) ->
  cand_equiv
    (mk_cand (fun v => forall C, cpred (F C) (tm_tapp v Ty_Nat)) Vi)
    (mk_cand (fun v => forall C, cpred (F' C) (tm_tapp v Ty_Nat)) Vi').
Proof.
  intros F F' Vi Vi' H. apply mk_cand_equiv. intros v. split;
    intros HV C.
  - apply (proj1 (H C (tm_tapp v Ty_Nat))). exact (HV C).
  - apply (proj2 (H C (tm_tapp v Ty_Nat))). exact (HV C).
Qed.

Lemma lc_ty_bvar_inv : forall k i, lc_ty_at k (Ty_BVar i) -> i < k.
Proof. intros. inversion H. assumption. Qed.

Lemma lc_ty_arrow_inv : forall k T1 T2,
  lc_ty_at k (Ty_Arrow T1 T2) -> lc_ty_at k T1 /\ lc_ty_at k T2.
Proof. intros. inversion H; subst; split; assumption. Qed.

Lemma lc_ty_all_inv : forall k T, lc_ty_at k (Ty_All T) -> lc_ty_at (S k) T.
Proof. intros. inversion H; subst; assumption. Qed.

Lemma interp_env_equiv : forall T k rho env env',
  lc_ty_at k T ->
  (forall i, i < k -> cand_equiv (env i) (env' i)) ->
  cand_equiv (interp rho env T) (interp rho env' T).
Proof.
  intros T. induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros k rho env env' Hlc Hagree t; simpl.
  - apply lc_ty_bvar_inv in Hlc. apply Hagree. assumption.
  - reflexivity.
  - apply lc_ty_arrow_inv in Hlc. destruct Hlc as [H1 H2].
    apply (arrow_cand_equiv (interp rho env T1) (interp rho env' T1)
                            (interp rho env T2) (interp rho env' T2)).
    + apply (IH1 k rho env env' H1 Hagree).
    + apply (IH2 k rho env env' H2 Hagree).
  - apply lc_ty_all_inv in Hlc.
    split.
    + intros [H1 [H2 H3]]. split; [exact H1|split; [exact H2|]].
      intros v Hm Hval C.
      assert (Henv : forall i, i < S k ->
        cand_equiv (cons_cand C env i) (cons_cand C env' i)).
      { intros i Hi. destruct i as [|j]; simpl.
        - apply cand_equiv_refl.
        - apply Hagree. lia. }
      apply (proj1 (IH1 (S k) rho (cons_cand C env) (cons_cand C env')
                         Hlc Henv (tm_tapp v Ty_Nat))).
      apply H3; assumption.
    + intros [H1 [H2 H3]]. split; [exact H1|split; [exact H2|]].
      intros v Hm Hval C.
      assert (Henv : forall i, i < S k ->
        cand_equiv (cons_cand C env i) (cons_cand C env' i)).
      { intros i Hi. destruct i as [|j]; simpl.
        - apply cand_equiv_refl.
        - apply Hagree. lia. }
      apply (proj2 (IH1 (S k) rho (cons_cand C env) (cons_cand C env')
                         Hlc Henv (tm_tapp v Ty_Nat))).
      apply H3; assumption.
  - reflexivity.
Qed.

Lemma interp_rho_equiv : forall T rho rho' env,
  (forall X, In X (fv_ty T) -> cand_equiv (rho X) (rho' X)) ->
  cand_equiv (interp rho env T) (interp rho' env T).
Proof.
  intros T. induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros rho rho' env Hagree t; simpl.
  - reflexivity.
  - apply Hagree. simpl. auto.
  - apply (arrow_cand_equiv (interp rho env T1) (interp rho' env T1)
                            (interp rho env T2) (interp rho' env T2)).
    + apply (IH1 rho rho' env). intros Y HY. apply Hagree. simpl.
      apply in_or_app. left. assumption.
    + apply (IH2 rho rho' env). intros Y HY. apply Hagree. simpl.
      apply in_or_app. right. assumption.
  - split.
    + intros [H1 [H2 H3]]. split; [exact H1|split; [exact H2|]].
      intros v Hm Hval C.
      apply (proj1 (IH1 rho rho' (cons_cand C env)
                         (fun Y HY => Hagree Y HY) (tm_tapp v Ty_Nat))).
      apply H3; assumption.
    + intros [H1 [H2 H3]]. split; [exact H1|split; [exact H2|]].
      intros v Hm Hval C.
      apply (proj2 (IH1 rho rho' (cons_cand C env)
                         (fun Y HY => Hagree Y HY) (tm_tapp v Ty_Nat))).
      apply H3; assumption.
  - reflexivity.
Qed.

Fixpoint insert_cand (k : nat) (C : cand) (env : nat -> cand) : nat -> cand :=
  match k with
  | O => cons_cand C env
  | S k' => fun i => match i with
                     | O => env O
                     | S j => insert_cand k' C (fun l => env (S l)) j
                     end
  end.

Lemma insert_cand_lt : forall k C env i, i < k -> insert_cand k C env i = env i.
Proof.
  intros k. induction k as [|k IH]; intros C env i Hi; [lia|].
  destruct i as [|j]; simpl.
  - reflexivity.
  - rewrite (IH C (fun l => env (S l)) j); [reflexivity | lia].
Qed.

Lemma insert_cand_cons : forall k C C2 env i,
  insert_cand (S k) C (cons_cand C2 env) i =
  cons_cand C2 (insert_cand k C env) i.
Proof.
  intros k C C2 env i. destruct i as [|j]; simpl; reflexivity.
Qed.

Lemma interp_open_at : forall T k U rho env,
  lc_ty_at k T -> lc_ty_at 0 U ->
  cand_equiv (interp rho env (open_ty_rec k U T))
             (interp rho (insert_cand k (interp rho env U) env) T).
Proof.
  intros T. induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros k U rho env Hlc HU t; simpl.
  - apply lc_ty_bvar_inv in Hlc.
    destruct (Nat.eqb k i) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + simpl. rewrite (insert_cand_lt k (interp rho env U) env i); [reflexivity | assumption].
  - reflexivity.
  - apply lc_ty_arrow_inv in Hlc. destruct Hlc as [H1 H2].
    apply (arrow_cand_equiv (interp rho env (open_ty_rec k U T1))
                            (interp rho (insert_cand k (interp rho env U) env) T1)
                            (interp rho env (open_ty_rec k U T2))
                            (interp rho (insert_cand k (interp rho env U) env) T2)).
    + apply (IH1 k U rho env H1 HU).
    + apply (IH2 k U rho env H2 HU).
  - apply lc_ty_all_inv in Hlc.
    split.
    + intros [H1 [H2 H3]]. split; [exact H1|split; [exact H2|]].
      intros v Hm Hval C.
      assert (H1C : cand_equiv
        (interp rho (cons_cand C env) (open_ty_rec (S k) U T1))
        (interp rho (insert_cand (S k) (interp rho (cons_cand C env) U) (cons_cand C env)) T1)).
      { apply (IH1 (S k) U rho (cons_cand C env) Hlc HU). }
      assert (Henv : forall i, i < S k ->
        cand_equiv
          (insert_cand (S k) (interp rho (cons_cand C env) U) (cons_cand C env) i)
          (cons_cand C (insert_cand k (interp rho env U) env) i)).
      { intros i Hi. destruct i as [|j].
        - simpl. apply cand_equiv_refl.
        - rewrite (insert_cand_lt (S k) (interp rho (cons_cand C env) U)
                     (cons_cand C env) (S j)); [| lia].
          simpl.
          rewrite (insert_cand_lt k (interp rho env U) env j); [| lia].
          apply cand_equiv_refl. }
      assert (H2C : cand_equiv
        (interp rho (insert_cand (S k) (interp rho (cons_cand C env) U) (cons_cand C env)) T1)
        (interp rho (cons_cand C (insert_cand k (interp rho env U) env)) T1)).
      { apply (interp_env_equiv T1 (S k) rho _ _ Hlc Henv). }
      apply (proj1 (H2C (tm_tapp v Ty_Nat))).
      apply (proj1 (H1C (tm_tapp v Ty_Nat))).
      apply H3; assumption.
    + intros [H1 [H2 H3]]. split; [exact H1|split; [exact H2|]].
      intros v Hm Hval C.
      assert (H1C : cand_equiv
        (interp rho (cons_cand C env) (open_ty_rec (S k) U T1))
        (interp rho (insert_cand (S k) (interp rho (cons_cand C env) U) (cons_cand C env)) T1)).
      { apply (IH1 (S k) U rho (cons_cand C env) Hlc HU). }
      assert (Henv : forall i, i < S k ->
        cand_equiv
          (insert_cand (S k) (interp rho (cons_cand C env) U) (cons_cand C env) i)
          (cons_cand C (insert_cand k (interp rho env U) env) i)).
      { intros i Hi. destruct i as [|j].
        - simpl. apply cand_equiv_refl.
        - rewrite (insert_cand_lt (S k) (interp rho (cons_cand C env) U)
                     (cons_cand C env) (S j)); [| lia].
          simpl.
          rewrite (insert_cand_lt k (interp rho env U) env j); [| lia].
          apply cand_equiv_refl. }
      assert (H2C : cand_equiv
        (interp rho (insert_cand (S k) (interp rho (cons_cand C env) U) (cons_cand C env)) T1)
        (interp rho (cons_cand C (insert_cand k (interp rho env U) env)) T1)).
      { apply (interp_env_equiv T1 (S k) rho _ _ Hlc Henv). }
      apply (proj2 (H1C (tm_tapp v Ty_Nat))).
      apply (proj2 (H2C (tm_tapp v Ty_Nat))).
      apply H3; assumption.
Qed.

Lemma interp_open_zero : forall T U rho env,
  lc_ty_at 1 T -> lc_ty_at 0 U ->
  cand_equiv (interp rho env (open_ty T U))
             (interp rho (cons_cand (interp rho env U) env) T).
Proof.
  intros. unfold open_ty.
  pose proof (interp_open_at T 0 U rho env H H0) as H1.
  exact H1.
Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationRecursionHardTask.
