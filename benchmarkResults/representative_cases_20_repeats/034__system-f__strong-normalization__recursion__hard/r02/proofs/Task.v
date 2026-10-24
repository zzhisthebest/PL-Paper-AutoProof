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

(* ================================================================ *)
(* Auxiliary infrastructure for the strong normalization proof      *)
(* ================================================================ *)

(* ---------- Fresh atoms ---------- *)

Fixpoint list_max (l : list atom) : atom :=
  match l with
  | nil => 0
  | cons x l' => Nat.max x (list_max l')
  end.

Lemma In_list_max : forall l x, In x l -> x <= list_max l.
Proof.
  induction l as [| y l IH]; intros x Hin; simpl in *.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; eauto | apply Nat.le_max_r].
Qed.

Definition fresh_atom (l : list atom) : atom := S (list_max l).

Lemma fresh_atom_notin : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l Hin. unfold fresh_atom in Hin.
  pose proof (In_list_max l (S (list_max l)) Hin). lia.
Qed.

(* ---------- Boolean equality helpers ---------- *)

Lemma eqb_true_eq : forall n m : nat, (n =? m) = true -> n = m.
Proof. intros n m E. apply Nat.eqb_eq. exact E. Qed.

Lemma eqb_false_neq : forall n m : nat, (n =? m) = false -> n <> m.
Proof. intros n m E H. apply Nat.eqb_eq in H. rewrite H in E. discriminate. Qed.

(* ---------- Free type atoms in types and terms ---------- *)

Fixpoint ftv_ty (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => nil
  | Ty_FVar X => cons X nil
  | Ty_Arrow T1 T2 => app (ftv_ty T1) (ftv_ty T2)
  | Ty_All T1 => ftv_ty T1
  | Ty_Nat => nil
  end.

Fixpoint ftv_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar _ => nil
  | tm_abs T t1 => app (ftv_ty T) (ftv_tm t1)
  | tm_app t1 t2 => app (ftv_tm t1) (ftv_tm t2)
  | tm_tabs t1 => ftv_tm t1
  | tm_tapp t1 T => app (ftv_tm t1) (ftv_ty T)
  | tm_zero => nil
  | tm_succ t1 => ftv_tm t1
  | tm_natrec n b s => app (app (ftv_tm n) (ftv_tm b)) (ftv_tm s)
  end.

Fixpoint fvars_tm (t : tm) : list atom :=
  match t with
  | tm_bvar _ => nil
  | tm_fvar x => cons x nil
  | tm_abs T t1 => fvars_tm t1
  | tm_app t1 t2 => app (fvars_tm t1) (fvars_tm t2)
  | tm_tabs t1 => fvars_tm t1
  | tm_tapp t1 T => fvars_tm t1
  | tm_zero => nil
  | tm_succ t1 => fvars_tm t1
  | tm_natrec n b s => app (app (fvars_tm n) (fvars_tm b)) (fvars_tm s)
  end.

Definition no_ftv_ty (T : ty) : Prop := forall X, ~ In X (ftv_ty T).
Definition no_ftv_tm (t : tm) : Prop := forall X, ~ In X (ftv_tm t).

Definition closed_ty (T : ty) : Prop := lc_ty_at 0 T /\ no_ftv_ty T.
Definition closed_tm (t : tm) : Prop := lc_tm_at 0 0 t /\ no_ftv_tm t.

(* ---------- Free atoms and opening ---------- *)

Lemma in_ftv_ty_open_ty_rec : forall X k V T,
  In X (ftv_ty (open_ty_rec k V T)) -> In X (ftv_ty T) \/ In X (ftv_ty V).
Proof.
  intros X k V T. revert k.
  induction T as [n | Y | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros k Hin; simpl in *.
  - destruct (Nat.eqb k n); simpl in *.
    + right; exact Hin.
    + destruct Hin.
  - left; exact Hin.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin].
    + destruct (IH1 k Hin) as [H | H]; auto.
    + destruct (IH2 k Hin) as [H | H]; auto.
  - apply IH1 in Hin. destruct Hin as [H | H]; auto.
  - destruct Hin.
Qed.

Lemma ftv_ty_subset_open_ty_rec : forall X k V T,
  In X (ftv_ty T) -> In X (ftv_ty (open_ty_rec k V T)).
Proof.
  intros X k V T. revert k.
  induction T as [n | Y | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros k Hin; simpl in *.
  - destruct (Nat.eqb k n); simpl in *; destruct Hin.
  - exact Hin.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin]; [left | right]; auto.
  - apply IH1. exact Hin.
  - destruct Hin.
Qed.

Lemma in_ftv_tm_open_tm_rec : forall X k u t,
  In X (ftv_tm (open_tm_rec k u t)) -> In X (ftv_tm t) \/ In X (ftv_tm u).
Proof.
  intros X k u t. revert k.
  induction t as [n | Y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T
                 | | t1 IH1 | n IHn b IHb s IHs];
    intros k Hin; simpl in *.
  - destruct (Nat.eqb k n); simpl in *.
    + right; exact Hin.
    + destruct Hin.
  - destruct Hin.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin].
    + left; auto.
    + destruct (IH1 (S k) Hin) as [H | H]; auto.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin].
    + destruct (IH1 k Hin) as [H | H]; auto.
    + destruct (IH2 k Hin) as [H | H]; auto.
  - apply IH1 in Hin. destruct Hin as [H | H]; auto.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin].
    + destruct (IH1 k Hin) as [H | H]; auto.
    + left; auto.
  - destruct Hin.
  - apply IH1 in Hin. destruct Hin as [H | H]; auto.
  - repeat rewrite in_app_iff in *.
    destruct Hin as [[Hin | Hin] | Hin].
    + destruct (IHn k Hin) as [H | H]; auto.
    + destruct (IHb k Hin) as [H | H]; auto.
    + destruct (IHs k Hin) as [H | H]; auto.
Qed.

Lemma ftv_tm_subset_open_tm_rec : forall X k u t,
  In X (ftv_tm t) -> In X (ftv_tm (open_tm_rec k u t)).
Proof.
  intros X k u t. revert k.
  induction t as [n | Y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T
                 | | t1 IH1 | n IHn b IHb s IHs];
    intros k Hin; simpl in *.
  - destruct (Nat.eqb k n); simpl in *; destruct Hin.
  - destruct Hin.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin].
    + left; auto.
    + right. apply (IH1 (S k)). exact Hin.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin]; [left | right]; auto.
  - apply IH1. exact Hin.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin]; [left | right]; auto.
  - destruct Hin.
  - apply IH1. exact Hin.
  - repeat rewrite in_app_iff in *. repeat rewrite in_app_iff.
    destruct Hin as [[Hin | Hin] | Hin]; [left; left | left; right | right]; auto.
Qed.

Lemma in_ftv_tm_open_tm_ty_rec : forall X k U t,
  In X (ftv_tm (open_tm_ty_rec k U t)) -> In X (ftv_tm t) \/ In X (ftv_ty U).
Proof.
  intros X k U t. revert k.
  induction t as [n | Y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T
                 | | t1 IH1 | n IHn b IHb s IHs];
    intros k Hin; simpl in *.
  - destruct Hin.
  - destruct Hin.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin].
    + destruct (in_ftv_ty_open_ty_rec X k U T Hin) as [H | H]; auto.
    + destruct (IH1 k Hin) as [H | H]; auto.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin].
    + destruct (IH1 k Hin) as [H | H]; auto.
    + destruct (IH2 k Hin) as [H | H]; auto.
  - apply IH1 in Hin. destruct Hin as [H | H]; auto.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin].
    + destruct (IH1 k Hin) as [H | H]; auto.
    + destruct (in_ftv_ty_open_ty_rec X k U T Hin) as [H | H]; auto.
  - destruct Hin.
  - apply IH1 in Hin. destruct Hin as [H | H]; auto.
  - repeat rewrite in_app_iff in *.
    destruct Hin as [[Hin | Hin] | Hin].
    + destruct (IHn k Hin) as [H | H]; auto.
    + destruct (IHb k Hin) as [H | H]; auto.
    + destruct (IHs k Hin) as [H | H]; auto.
Qed.

Lemma ftv_tm_subset_open_tm_ty_rec : forall X k U t,
  In X (ftv_tm t) -> In X (ftv_tm (open_tm_ty_rec k U t)).
Proof.
  intros X k U t. revert k.
  induction t as [n | Y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T
                 | | t1 IH1 | n IHn b IHb s IHs];
    intros k Hin; simpl in *.
  - destruct Hin.
  - destruct Hin.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin].
    + left. apply ftv_ty_subset_open_ty_rec. exact Hin.
    + right. apply IH1. exact Hin.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin]; [left | right]; auto.
  - apply IH1. exact Hin.
  - apply in_app_iff in Hin. rewrite in_app_iff.
    destruct Hin as [Hin | Hin].
    + left. apply IH1. exact Hin.
    + right. apply ftv_ty_subset_open_ty_rec. exact Hin.
  - destruct Hin.
  - apply IH1. exact Hin.
  - repeat rewrite in_app_iff in *. repeat rewrite in_app_iff.
    destruct Hin as [[Hin | Hin] | Hin]; [left; left | left; right | right]; auto.
Qed.

(* ---------- Parallel substitution of free type atoms and free term vars ---------- *)

Definition tysub := atom -> ty.
Definition tmsub := atom -> tm.

Fixpoint ty_subst_env (sT : tysub) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sT X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst_env sT T1) (ty_subst_env sT T2)
  | Ty_All T1 => Ty_All (ty_subst_env sT T1)
  | Ty_Nat => Ty_Nat
  end.

Fixpoint tm_subst_env (sT : tysub) (s : tmsub) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => s x
  | tm_abs T t1 => tm_abs (ty_subst_env sT T) (tm_subst_env sT s t1)
  | tm_app t1 t2 => tm_app (tm_subst_env sT s t1) (tm_subst_env sT s t2)
  | tm_tabs t1 => tm_tabs (tm_subst_env sT s t1)
  | tm_tapp t1 T => tm_tapp (tm_subst_env sT s t1) (ty_subst_env sT T)
  | tm_zero => tm_zero
  | tm_succ t1 => tm_succ (tm_subst_env sT s t1)
  | tm_natrec n b g =>
      tm_natrec (tm_subst_env sT s n) (tm_subst_env sT s b) (tm_subst_env sT s g)
  end.

Definition extend_ty (sT : tysub) (X : atom) (U : ty) : tysub :=
  fun Y => if Nat.eqb Y X then U else sT Y.

Definition extend_tm (s : tmsub) (x : atom) (u : tm) : tmsub :=
  fun y => if Nat.eqb y x then u else s y.

Lemma extend_ty_eq : forall sT X U, extend_ty sT X U X = U.
Proof.
  intros sT X U. unfold extend_ty.
  destruct (Nat.eqb X X) eqn:E; auto.
  apply eqb_false_neq in E. exfalso; apply (E eq_refl).
Qed.

Lemma extend_ty_neq : forall sT X U Y, Y <> X -> extend_ty sT X U Y = sT Y.
Proof.
  intros sT X U Y Hne. unfold extend_ty.
  destruct (Nat.eqb Y X) eqn:E; auto.
  apply eqb_true_eq in E. exfalso; auto.
Qed.

Lemma extend_tm_eq : forall s x u, extend_tm s x u x = u.
Proof.
  intros s x u. unfold extend_tm.
  destruct (Nat.eqb x x) eqn:E; auto.
  apply eqb_false_neq in E. exfalso; apply (E eq_refl).
Qed.

Lemma extend_tm_neq : forall s x u y, y <> x -> extend_tm s x u y = s y.
Proof.
  intros s x u y Hne. unfold extend_tm.
  destruct (Nat.eqb y x) eqn:E; auto.
  apply eqb_true_eq in E. exfalso; auto.
Qed.

Lemma ty_subst_env_no_ftv : forall sT T,
  (forall X, no_ftv_ty (sT X)) -> no_ftv_ty (ty_subst_env sT T).
Proof.
  intros sT T Hs X Hin. revert Hin.
  induction T as [n | Y | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros Hin; simpl in *.
  - destruct Hin.
  - exact (Hs Y X Hin).
  - rewrite in_app_iff in Hin.
    destruct Hin as [H | H]; [exact (IH1 H) | exact (IH2 H)].
  - exact (IH1 Hin).
  - destruct Hin.
Qed.

Lemma tm_subst_env_no_ftv : forall sT s t,
  (forall X, no_ftv_ty (sT X)) ->
  (forall x, no_ftv_tm (s x)) ->
  no_ftv_tm (tm_subst_env sT s t).
Proof.
  intros sT s t HT Hs X Hin. revert Hin.
  induction t as [n | Y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T
                 | | t1 IH1 | n IHn b IHb g IHg];
    intros Hin; simpl in *.
  - destruct Hin.
  - exact (Hs Y X Hin).
  - rewrite in_app_iff in Hin. destruct Hin as [H | H].
    + exact (ty_subst_env_no_ftv sT T HT X H).
    + exact (IH1 H).
  - rewrite in_app_iff in Hin. destruct Hin as [H | H].
    + exact (IH1 H).
    + exact (IH2 H).
  - exact (IH1 Hin).
  - rewrite in_app_iff in Hin. destruct Hin as [H | H].
    + exact (IH1 H).
    + exact (ty_subst_env_no_ftv sT T HT X H).
  - destruct Hin.
  - exact (IH1 Hin).
  - repeat rewrite in_app_iff in Hin.
    destruct Hin as [[H | H] | H].
    + exact (IHn H).
    + exact (IHb H).
    + exact (IHg H).
Qed.

(* ---------- Local closure lemmas ---------- *)

Lemma lc_ty_at_weaken : forall T K, lc_ty_at K T ->
  forall K', K <= K' -> lc_ty_at K' T.
Proof.
  intros T K H. induction H as
    [k i Hlt | k X | k T1 T2 H1 IH1 H2 IH2 | k T0 H1 IH1 | k];
    intros K' HK; simpl.
  - apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow.
    + exact (IH1 K' HK).
    + exact (IH2 K' HK).
  - apply lc_ty_all. apply IH1. lia.
  - apply lc_ty_nat.
Qed.

Lemma lc_tm_at_weaken : forall t K k, lc_tm_at K k t ->
  forall K' k', K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros t K k H. induction H as
    [K0 k0 i Hlt | K0 k0 x | K0 k0 T0 t0 Hty Hsub IHt | K0 k0 t1 t2 H1 IH1 H2 IH2
    | K0 k0 t0 Hsub IHt | K0 k0 t0 T0 H1 IHt Hty | K0 k0 | K0 k0 t0 Hsub IHt
    | K0 k0 n b g Hn IHn Hb IHb Hg IHg];
    intros K' k' HK' Hk'; simpl.
  - apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + exact (lc_ty_at_weaken T0 K0 Hty K' HK').
    + apply IHt; lia.
  - apply lc_tm_app.
    + exact (IH1 K' k' HK' Hk').
    + exact (IH2 K' k' HK' Hk').
  - apply lc_tm_tabs. apply IHt; lia.
  - apply lc_tm_tapp.
    + exact (IHt K' k' HK' Hk').
    + exact (lc_ty_at_weaken T0 K0 Hty K' HK').
  - apply lc_tm_zero.
  - apply lc_tm_succ. exact (IHt K' k' HK' Hk').
  - apply lc_tm_rec.
    + exact (IHn K' k' HK' Hk').
    + exact (IHb K' k' HK' Hk').
    + exact (IHg K' k' HK' Hk').
Qed.

Lemma lc_ty_at_open_aux : forall T K, lc_ty_at K T ->
  forall j V, K = S j -> lc_ty_at j V -> lc_ty_at j (open_ty_rec j V T).
Proof.
  intros T K H. induction H as
    [k i Hlt | k X | k T1 T2 H1 IH1 H2 IH2 | k T0 H1 IH1 | k];
    intros j V Heq HV; simpl.
  - subst k. destruct (Nat.eqb j i) eqn:E; simpl.
    + apply eqb_true_eq in E. subst i. exact HV.
    + apply eqb_false_neq in E. apply lc_ty_bvar. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - apply lc_ty_all. apply IH1 with (j := S j).
    + lia.
    + apply lc_ty_at_weaken with (K := j); [assumption | lia].
  - apply lc_ty_nat.
Qed.

Lemma lc_ty_at_open : forall j U T,
  lc_ty_at (S j) T -> lc_ty_at j U -> lc_ty_at j (open_ty_rec j U T).
Proof.
  intros j U T H HU. apply (lc_ty_at_open_aux T (S j) H j U eq_refl HU).
Qed.

Lemma lc_ty_at_open_inv : forall j U T,
  lc_ty_at j (open_ty_rec j U T) -> lc_ty_at (S j) T.
Proof.
  intros j U T. revert j U.
  induction T as [n | Y | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros j U HT; simpl in *.
  - destruct (Nat.eqb j n) eqn:E; simpl in *.
    + apply eqb_true_eq in E. subst n. apply lc_ty_bvar. lia.
    + apply lc_ty_bvar. inversion HT; subst. lia.
  - apply lc_ty_fvar.
  - apply lc_ty_arrow.
    + apply IH1 with (j := j) (U := U). inversion HT; subst; assumption.
    + apply IH2 with (j := j) (U := U). inversion HT; subst; assumption.
  - apply lc_ty_all.
    apply IH1 with (j := S j) (U := U). inversion HT; subst; assumption.
  - apply lc_ty_nat.
Qed.

Lemma lc_ty_at_open_rec_any : forall T K, lc_ty_at K T ->
  forall k V, K <= k -> open_ty_rec k V T = T.
Proof.
  intros T K H. induction H as
    [k i Hlt | k X | k T1 T2 H1 IH1 H2 IH2 | k T0 H1 IH1 | k];
    intros k0 V HK; simpl.
  - destruct (Nat.eqb k0 i) eqn:E; auto.
    apply eqb_true_eq in E. lia.
  - reflexivity.
  - rewrite (IH1 k0 V HK). rewrite (IH2 k0 V HK). reflexivity.
  - assert (Hr : open_ty_rec (S k0) V T0 = T0) by (apply IH1; lia).
    rewrite Hr. reflexivity.
  - reflexivity.
Qed.

Lemma lc_tm_at_open_tm : forall t K k, lc_tm_at K k t ->
  forall j u, k = S j -> lc_tm_at K 0 u ->
  lc_tm_at K j (open_tm_rec j u t).
Proof.
  intros t K k H. induction H as
    [K0 k0 i Hlt | K0 k0 x | K0 k0 T0 t0 Hty Hsub IHt | K0 k0 t1 t2 H1 IH1 H2 IH2
    | K0 k0 t0 Hsub IHt | K0 k0 t0 T0 H1 IHt Hty | K0 k0 | K0 k0 t0 Hsub IHt
    | K0 k0 n b g Hn IHn Hb IHb Hg IHg];
    intros j u Heq HU; simpl.
  - subst k0. destruct (Nat.eqb j i) eqn:E; simpl.
    + apply eqb_true_eq in E. subst i.
      apply lc_tm_at_weaken with (K := K0) (k := 0); [assumption | lia | lia].
    + apply eqb_false_neq in E. apply lc_tm_bvar. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + assumption.
    + apply IHt with (j := S j).
      * lia.
      * assumption.
  - apply lc_tm_app.
    + apply IH1 with (j := j); assumption.
    + apply IH2 with (j := j); assumption.
  - apply lc_tm_tabs.
    apply IHt.
    + assumption.
    + apply lc_tm_at_weaken with (K := K0) (k := 0); [assumption | lia | lia].
  - apply lc_tm_tapp.
    + apply IHt with (j := j); assumption.
    + assumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ. apply IHt with (j := j); assumption.
  - apply lc_tm_rec.
    + apply IHn with (j := j); assumption.
    + apply IHb with (j := j); assumption.
    + apply IHg with (j := j); assumption.
Qed.

Lemma lc_tm_at_open_tm_inv : forall t k u K,
  lc_tm_at K k (open_tm_rec k u t) -> lc_tm_at K (S k) t.
Proof.
  induction t as [n | Y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T
                 | | t1 IH1 | n IHn b IHb g IHg];
    intros k u K HT; simpl in *.
  - destruct (Nat.eqb k n) eqn:E; simpl in *.
    + apply eqb_true_eq in E. subst n. apply lc_tm_bvar. lia.
    + apply lc_tm_bvar. inversion HT; subst. lia.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + inversion HT; subst; assumption.
    + apply IH1 with (k := S k) (u := u). inversion HT; subst; assumption.
  - apply lc_tm_app.
    + apply IH1 with (k := k) (u := u). inversion HT; subst; assumption.
    + apply IH2 with (k := k) (u := u). inversion HT; subst; assumption.
  - apply lc_tm_tabs.
    apply IH1 with (K := S K) (k := k) (u := u). inversion HT; subst; assumption.
  - apply lc_tm_tapp.
    + apply IH1 with (k := k) (u := u). inversion HT; subst; assumption.
    + inversion HT; subst; assumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ.
    apply IH1 with (k := k) (u := u). inversion HT; subst; assumption.
  - apply lc_tm_rec.
    + apply IHn with (k := k) (u := u). inversion HT; subst; assumption.
    + apply IHb with (k := k) (u := u). inversion HT; subst; assumption.
    + apply IHg with (k := k) (u := u). inversion HT; subst; assumption.
Qed.

Lemma lc_tm_at_open_ty : forall t K k, lc_tm_at K k t ->
  forall j U, K = S j -> lc_ty_at j U ->
  lc_tm_at j k (open_tm_ty_rec j U t).
Proof.
  intros t K k H. induction H as
    [K0 k0 i Hlt | K0 k0 x | K0 k0 T0 t0 Hty Hsub IHt | K0 k0 t1 t2 H1 IH1 H2 IH2
    | K0 k0 t0 Hsub IHt | K0 k0 t0 T0 H1 IHt Hty | K0 k0 | K0 k0 t0 Hsub IHt
    | K0 k0 n b g Hn IHn Hb IHb Hg IHg];
    intros j U Heq HU; simpl.
  - subst K0. apply lc_tm_bvar. assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_at_open with (j := j); [rewrite <- Heq; assumption | assumption].
    + apply IHt with (j := j); assumption.
  - apply lc_tm_app.
    + apply IH1 with (j := j); assumption.
    + apply IH2 with (j := j); assumption.
  - apply lc_tm_tabs.
    apply IHt with (j := S j).
    + lia.
    + apply lc_ty_at_weaken with (K := j); [assumption | lia].
  - apply lc_tm_tapp.
    + apply IHt with (j := j); assumption.
    + apply lc_ty_at_open with (j := j); [rewrite <- Heq; assumption | assumption].
  - apply lc_tm_zero.
  - apply lc_tm_succ. apply IHt with (j := j); assumption.
  - apply lc_tm_rec.
    + apply IHn with (j := j); assumption.
    + apply IHb with (j := j); assumption.
    + apply IHg with (j := j); assumption.
Qed.

Corollary lc_tm_at_open_tm_0 : forall t k u,
  lc_tm_at 0 (S k) t -> lc_tm_at 0 0 u -> lc_tm_at 0 k (open_tm_rec k u t).
Proof. intros. eapply lc_tm_at_open_tm; eauto. Qed.

Corollary lc_tm_at_open_ty_0 : forall t k U,
  lc_tm_at 1 k t -> lc_ty_at 0 U -> lc_tm_at 0 k (open_tm_ty_rec 0 U t).
Proof. intros. eapply lc_tm_at_open_ty; eauto. Qed.

Lemma lc_tm_at_open_ty_inv : forall j k U t,
  lc_tm_at j k (open_tm_ty_rec j U t) -> lc_tm_at (S j) k t.
Proof.
  intros j k U t. revert j k U.
  induction t as [n | Y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T
                 | | t1 IH1 | n IHn b IHb g IHg];
    intros j k U HT; simpl in *.
  - apply lc_tm_bvar. inversion HT; subst. assumption.
  - apply lc_tm_fvar.
  - apply lc_tm_abs.
    + apply lc_ty_at_open_inv with (j := j) (U := U). inversion HT; subst; assumption.
    + apply IH1 with (j := j) (U := U). inversion HT; subst; assumption.
  - apply lc_tm_app.
    + apply IH1 with (j := j) (U := U). inversion HT; subst; assumption.
    + apply IH2 with (j := j) (U := U). inversion HT; subst; assumption.
  - apply lc_tm_tabs.
    apply IH1 with (j := S j) (U := U). inversion HT; subst; assumption.
  - apply lc_tm_tapp.
    + apply IH1 with (j := j) (U := U). inversion HT; subst; assumption.
    + apply lc_ty_at_open_inv with (j := j) (U := U). inversion HT; subst; assumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ.
    apply IH1 with (j := j) (U := U). inversion HT; subst; assumption.
  - apply lc_tm_rec.
    + apply IHn with (j := j) (U := U). inversion HT; subst; assumption.
    + apply IHb with (j := j) (U := U). inversion HT; subst; assumption.
    + apply IHg with (j := j) (U := U). inversion HT; subst; assumption.
Qed.

(* ---------- Substitution preserves local closure ---------- *)

Lemma ty_subst_env_lc : forall sT K T,
  lc_ty_at K T -> (forall X, lc_ty_at 0 (sT X)) ->
  lc_ty_at K (ty_subst_env sT T).
Proof.
  intros sT K T H. revert sT.
  induction H as
    [k i Hlt | k X | k T1 T2 H1 IH1 H2 IH2 | k T0 H1 IH1 | k];
    intros sT Hc; simpl.
  - apply lc_ty_bvar. assumption.
  - apply lc_ty_at_weaken with (K := 0); [apply Hc | lia].
  - apply lc_ty_arrow.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - apply lc_ty_all. apply IH1; assumption.
  - apply lc_ty_nat.
Qed.

Lemma tm_subst_env_lc : forall sT s K k t,
  lc_tm_at K k t ->
  (forall X, lc_ty_at 0 (sT X)) ->
  (forall x, lc_tm_at 0 0 (s x)) ->
  lc_tm_at K k (tm_subst_env sT s t).
Proof.
  intros sT s K k t H. revert sT s.
  induction H as
    [K0 k0 i Hlt | K0 k0 x | K0 k0 T0 t0 Hty Hsub IHt | K0 k0 t1 t2 H1 IH1 H2 IH2
    | K0 k0 t0 Hsub IHt | K0 k0 t0 T0 H1 IHt Hty | K0 k0 | K0 k0 t0 Hsub IHt
    | K0 k0 n b g Hn IHn Hb IHb Hg IHg];
    intros sT0 s0 Hc Hs; simpl.
  - apply lc_tm_bvar. assumption.
  - apply lc_tm_at_weaken with (K := 0) (k := 0); [apply Hs | lia | lia].
  - apply lc_tm_abs.
    + apply ty_subst_env_lc; assumption.
    + apply IHt; assumption.
  - apply lc_tm_app.
    + apply IH1; assumption.
    + apply IH2; assumption.
  - apply lc_tm_tabs. apply IHt; assumption.
  - apply lc_tm_tapp.
    + apply IHt; assumption.
    + apply ty_subst_env_lc; assumption.
  - apply lc_tm_zero.
  - apply lc_tm_succ. apply IHt; assumption.
  - apply lc_tm_rec.
    + apply IHn; assumption.
    + apply IHb; assumption.
    + apply IHg; assumption.
Qed.

(* ---------- Commutation of substitution with opening ---------- *)

Lemma lc_tm_at_open_rec_any : forall t K k, lc_tm_at K k t ->
  forall k' u, k <= k' -> open_tm_rec k' u t = t.
Proof.
  intros t K k H. induction H as
    [K0 k0 i Hlt | K0 k0 x | K0 k0 T0 t0 Hty Hsub IHt | K0 k0 t1 t2 H1 IH1 H2 IH2
    | K0 k0 t0 Hsub IHt | K0 k0 t0 T0 H1 IHt Hty | K0 k0 | K0 k0 t0 Hsub IHt
    | K0 k0 n b g Hn IHn Hb IHb Hg IHg];
    intros k' u Hk'; simpl.
  - destruct (Nat.eqb k' i) eqn:E.
    + apply eqb_true_eq in E. exfalso. lia.
    + reflexivity.
  - reflexivity.
  - assert (Hr : open_tm_rec (S k') u t0 = t0) by (apply IHt; lia).
    rewrite Hr. reflexivity.
  - rewrite (IH1 k' u Hk'). rewrite (IH2 k' u Hk'). reflexivity.
  - rewrite (IHt k' u Hk'). reflexivity.
  - rewrite (IHt k' u Hk'). reflexivity.
  - reflexivity.
  - rewrite (IHt k' u Hk'). reflexivity.
  - rewrite (IHn k' u Hk'). rewrite (IHb k' u Hk'). rewrite (IHg k' u Hk').
    reflexivity.
Qed.

Lemma lc_tm_at_open_ty_rec_any : forall t K k, lc_tm_at K k t ->
  forall j U, K <= j -> open_tm_ty_rec j U t = t.
Proof.
  intros t K k H. induction H as
    [K0 k0 i Hlt | K0 k0 x | K0 k0 T0 t0 Hty Hsub IHt | K0 k0 t1 t2 H1 IH1 H2 IH2
    | K0 k0 t0 Hsub IHt | K0 k0 t0 T0 H1 IHt Hty | K0 k0 | K0 k0 t0 Hsub IHt
    | K0 k0 n b g Hn IHn Hb IHb Hg IHg];
    intros j U Hj; simpl.
  - reflexivity.
  - reflexivity.
  - assert (Hr : open_ty_rec j U T0 = T0).
    { apply lc_ty_at_open_rec_any with (K := K0); [assumption | assumption]. }
    rewrite Hr. rewrite (IHt j U Hj). reflexivity.
  - rewrite (IH1 j U Hj). rewrite (IH2 j U Hj). reflexivity.
  - assert (Hr : open_tm_ty_rec (S j) U t0 = t0) by (apply IHt; lia).
    rewrite Hr. reflexivity.
  - assert (Hr : open_ty_rec j U T0 = T0).
    { apply lc_ty_at_open_rec_any with (K := K0); [assumption | assumption]. }
    rewrite (IHt j U Hj). rewrite Hr. reflexivity.
  - reflexivity.
  - rewrite (IHt j U Hj). reflexivity.
  - rewrite (IHn j U Hj). rewrite (IHb j U Hj). rewrite (IHg j U Hj). reflexivity.
Qed.

Lemma ty_subst_env_open_ty_rec : forall sT k U T,
  (forall Y, lc_ty_at 0 (sT Y)) ->
  ty_subst_env sT (open_ty_rec k U T) =
  open_ty_rec k (ty_subst_env sT U) (ty_subst_env sT T).
Proof.
  intros sT k U T. revert k U.
  induction T as [n | Y | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros k U Hc; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply lc_ty_at_open_rec_any with (K := 0); [apply Hc | lia].
  - rewrite (IH1 k U Hc). rewrite (IH2 k U Hc). reflexivity.
  - rewrite (IH1 (S k) U Hc). reflexivity.
  - reflexivity.
Qed.

Lemma ty_subst_env_open_ty_FVar : forall sT X U k T,
  (forall Y, lc_ty_at 0 (sT Y)) ->
  ~ In X (ftv_ty T) ->
  ty_subst_env (extend_ty sT X U) (open_ty_rec k (Ty_FVar X) T) =
  open_ty_rec k U (ty_subst_env sT T).
Proof.
  intros sT X U k T. revert k.
  induction T as [n | Y | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros k Hc Hfresh; simpl in *.
  - destruct (Nat.eqb k n); simpl.
    + rewrite extend_ty_eq. reflexivity.
    + reflexivity.
  - assert (Hne : Y <> X) by (intro H; apply Hfresh; simpl; subst; auto).
    rewrite (extend_ty_neq sT X U Y Hne).
    symmetry. apply lc_ty_at_open_rec_any with (K := 0); [apply Hc | lia].
  - assert (H1 : ~ In X (ftv_ty T1)).
    { intro H. apply Hfresh. rewrite in_app_iff. left. assumption. }
    assert (H2 : ~ In X (ftv_ty T2)).
    { intro H. apply Hfresh. rewrite in_app_iff. right. assumption. }
    rewrite (IH1 k Hc H1). rewrite (IH2 k Hc H2). reflexivity.
  - rewrite (IH1 (S k) Hc Hfresh). reflexivity.
  - reflexivity.
Qed.

Lemma tm_subst_env_open_tm_rec : forall sT s k u t,
  (forall x, lc_tm_at 0 0 (s x)) ->
  tm_subst_env sT s (open_tm_rec k u t) =
  open_tm_rec k (tm_subst_env sT s u) (tm_subst_env sT s t).
Proof.
  intros sT s k u t. revert k u.
  induction t as [n | Y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T
                 | | t1 IH1 | n IHn b IHb g IHg];
    intros k u Hc; simpl.
  - destruct (Nat.eqb k n); reflexivity.
  - symmetry. apply lc_tm_at_open_rec_any with (K := 0) (k := 0); [apply Hc | lia].
  - rewrite (IH1 (S k) u Hc). reflexivity.
  - rewrite (IH1 k u Hc). rewrite (IH2 k u Hc). reflexivity.
  - rewrite (IH1 k u Hc). reflexivity.
  - rewrite (IH1 k u Hc). reflexivity.
  - reflexivity.
  - rewrite (IH1 k u Hc). reflexivity.
  - rewrite (IHn k u Hc). rewrite (IHb k u Hc). rewrite (IHg k u Hc). reflexivity.
Qed.

Lemma tm_subst_env_open_tm_ty_rec : forall sT s k U t,
  (forall Y, lc_ty_at 0 (sT Y)) ->
  (forall x, lc_tm_at 0 0 (s x)) ->
  tm_subst_env sT s (open_tm_ty_rec k U t) =
  open_tm_ty_rec k (ty_subst_env sT U) (tm_subst_env sT s t).
Proof.
  intros sT s k U t. revert k U.
  induction t as [n | Y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T
                 | | t1 IH1 | n IHn b IHb g IHg];
    intros k U HcT Hc; simpl.
  - reflexivity.
  - symmetry. apply lc_tm_at_open_ty_rec_any with (K := 0) (k := 0); [apply Hc | lia].
  - rewrite (ty_subst_env_open_ty_rec sT k U T HcT).
    rewrite (IH1 k U HcT Hc). reflexivity.
  - rewrite (IH1 k U HcT Hc). rewrite (IH2 k U HcT Hc). reflexivity.
  - rewrite (IH1 (S k) U HcT Hc). reflexivity.
  - rewrite (IH1 k U HcT Hc). rewrite (ty_subst_env_open_ty_rec sT k U T HcT).
    reflexivity.
  - reflexivity.
  - rewrite (IH1 k U HcT Hc). reflexivity.
  - rewrite (IHn k U HcT Hc). rewrite (IHb k U HcT Hc). rewrite (IHg k U HcT Hc).
    reflexivity.
Qed.

Lemma tm_subst_env_open_tm_ty_FVar : forall sT s X U k t,
  (forall Y, lc_ty_at 0 (sT Y)) ->
  (forall x, lc_tm_at 0 0 (s x)) ->
  ~ In X (ftv_tm t) ->
  tm_subst_env (extend_ty sT X U) s (open_tm_ty_rec k (Ty_FVar X) t) =
  open_tm_ty_rec k U (tm_subst_env sT s t).
Proof.
  intros sT s X U k t. revert k.
  induction t as [n | Y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T
                 | | t1 IH1 | n IHn b IHb g IHg];
    intros k HcT Hc Hfresh; simpl in *.
  - reflexivity.
  - symmetry. apply lc_tm_at_open_ty_rec_any with (K := 0) (k := 0); [apply Hc | lia].
  - assert (H1 : ~ In X (ftv_ty T)).
    { intro H. apply Hfresh. rewrite in_app_iff. left. assumption. }
    assert (H2 : ~ In X (ftv_tm t1)).
    { intro H. apply Hfresh. rewrite in_app_iff. right. assumption. }
    rewrite (ty_subst_env_open_ty_FVar sT X U k T HcT H1).
    rewrite (IH1 k HcT Hc H2). reflexivity.
  - assert (H1 : ~ In X (ftv_tm t1)).
    { intro H. apply Hfresh. rewrite in_app_iff. left. assumption. }
    assert (H2 : ~ In X (ftv_tm t2)).
    { intro H. apply Hfresh. rewrite in_app_iff. right. assumption. }
    rewrite (IH1 k HcT Hc H1). rewrite (IH2 k HcT Hc H2). reflexivity.
  - rewrite (IH1 (S k) HcT Hc Hfresh). reflexivity.
  - assert (H1 : ~ In X (ftv_tm t1)).
    { intro H. apply Hfresh. rewrite in_app_iff. left. assumption. }
    assert (H2 : ~ In X (ftv_ty T)).
    { intro H. apply Hfresh. rewrite in_app_iff. right. assumption. }
    rewrite (IH1 k HcT Hc H1).
    rewrite (ty_subst_env_open_ty_FVar sT X U k T HcT H2). reflexivity.
  - reflexivity.
  - rewrite (IH1 k HcT Hc Hfresh). reflexivity.
  - assert (H1 : ~ In X (ftv_tm n)).
    { intro H. apply Hfresh. rewrite in_app_iff. left. rewrite in_app_iff. left. assumption. }
    assert (H2 : ~ In X (ftv_tm b)).
    { intro H. apply Hfresh. rewrite in_app_iff. left. rewrite in_app_iff. right. assumption. }
    assert (H3 : ~ In X (ftv_tm g)).
    { intro H. apply Hfresh. rewrite in_app_iff. right. assumption. }
    rewrite (IHn k HcT Hc H1). rewrite (IHb k HcT Hc H2).
    rewrite (IHg k HcT Hc H3). reflexivity.
Qed.

(* ---------- Agreement lemmas for substitution environments ---------- *)

Lemma ty_subst_env_agree : forall s1 s2 T,
  (forall X, In X (ftv_ty T) -> s1 X = s2 X) ->
  ty_subst_env s1 T = ty_subst_env s2 T.
Proof.
  intros s1 s2 T. revert s1 s2.
  induction T as [n | Y | T1 IH1 T2 IH2 | T1 IH1 | ];
    intros s1 s2 Hag; simpl in *.
  - reflexivity.
  - apply Hag. simpl. auto.
  - assert (E1 : ty_subst_env s1 T1 = ty_subst_env s2 T1).
    { apply IH1. intros X H. apply Hag. rewrite in_app_iff. left. assumption. }
    assert (E2 : ty_subst_env s1 T2 = ty_subst_env s2 T2).
    { apply IH2. intros X H. apply Hag. rewrite in_app_iff. right. assumption. }
    rewrite E1, E2. reflexivity.
  - assert (E1 : ty_subst_env s1 T1 = ty_subst_env s2 T1).
    { apply IH1. intros X H. apply Hag. assumption. }
    rewrite E1. reflexivity.
  - reflexivity.
Qed.

Lemma tm_subst_env_agree : forall sT s1 s2 t,
  (forall x, In x (fvars_tm t) -> s1 x = s2 x) ->
  tm_subst_env sT s1 t = tm_subst_env sT s2 t.
Proof.
  intros sT s1 s2 t. revert s1 s2.
  induction t as [n | Y | T t1 IH1 | t1 IH1 t2 IH2 | t1 IH1 | t1 IH1 T
                 | | t1 IH1 | n IHn b IHb g IHg];
    intros s1 s2 Hag; simpl in *.
  - reflexivity.
  - apply Hag. simpl. auto.
  - rewrite (IH1 s1 s2). reflexivity.
    intros x H. apply Hag. assumption.
  - assert (E1 : tm_subst_env sT s1 t1 = tm_subst_env sT s2 t1).
    { apply IH1. intros x H. apply Hag. rewrite in_app_iff. left. assumption. }
    assert (E2 : tm_subst_env sT s1 t2 = tm_subst_env sT s2 t2).
    { apply IH2. intros x H. apply Hag. rewrite in_app_iff. right. assumption. }
    rewrite E1, E2. reflexivity.
  - rewrite (IH1 s1 s2). reflexivity.
    intros x H. apply Hag. assumption.
  - rewrite (IH1 s1 s2). reflexivity.
    intros x H. apply Hag. assumption.
  - reflexivity.
  - rewrite (IH1 s1 s2). reflexivity.
    intros x H. apply Hag. assumption.
  - assert (E1 : tm_subst_env sT s1 n = tm_subst_env sT s2 n).
    { apply IHn. intros x H. apply Hag. rewrite in_app_iff. left. rewrite in_app_iff. left. assumption. }
    assert (E2 : tm_subst_env sT s1 b = tm_subst_env sT s2 b).
    { apply IHb. intros x H. apply Hag. rewrite in_app_iff. left. rewrite in_app_iff. right. assumption. }
    assert (E3 : tm_subst_env sT s1 g = tm_subst_env sT s2 g).
    { apply IHg. intros x H. apply Hag. rewrite in_app_iff. right. assumption. }
    rewrite E1, E2, E3. reflexivity.
Qed.

(* ---------- Values and reduction sequences ---------- *)

Lemma numeric_value_lc : forall n, numeric_value n -> lc_tm_at 0 0 n.
Proof.
  intros n H. induction H as [| m Hm IH].
  - apply lc_tm_zero.
  - apply lc_tm_succ. assumption.
Qed.

Lemma value_lc : forall v, value v -> lc_tm_at 0 0 v.
Proof.
  intros v H. destruct H as [T t Hlc | t Hlc | n Hn].
  - assumption.
  - assumption.
  - apply numeric_value_lc. assumption.
Qed.

Lemma numeric_value_no_step : forall n, numeric_value n -> forall u, step n u -> False.
Proof.
  intros n H. induction H as [| m Hm IH]; intros u Hs.
  - inversion Hs.
  - inversion Hs; subst. eapply IH; eauto.
Qed.

Lemma value_no_step : forall v u, value v -> step v u -> False.
Proof.
  intros v u Hv Hs. destruct Hv as [T t Hlc | t Hlc | n Hn].
  - inversion Hs.
  - inversion Hs.
  - eapply numeric_value_no_step; eauto.
Qed.

Lemma sn_value : forall v, value v -> strongly_normalizing v.
Proof.
  intros v Hv. apply SN_intro. intros u Hs. exfalso. eapply value_no_step; eauto.
Qed.

Lemma multi_trans : forall a b, multi a b -> forall c, multi b c -> multi a c.
Proof.
  intros a b H. induction H as [x | x y z Hstep Hrest IH]; intros c Hbc.
  - assumption.
  - apply multi_step with (y := y); [assumption | apply IH; assumption].
Qed.

Lemma multi_inv : forall a c, multi a c ->
  a = c \/ (exists b, step a b /\ multi b c).
Proof.
  intros a c H. destruct H as [x | x y z Hstep Hrest].
  - left; reflexivity.
  - right; exists y; split; assumption.
Qed.

Lemma multi_value : forall t v, multi t v -> value t -> v = t.
Proof.
  intros t v H. induction H as [x | x y z Hstep Hrest IH]; intro Hv.
  - reflexivity.
  - exfalso. eapply value_no_step; eauto.
Qed.

(* ---------- Inversion helpers for local closure ---------- *)

Lemma lc_app_inv : forall t1 t2, lc_tm_at 0 0 (tm_app t1 t2) ->
  lc_tm_at 0 0 t1 /\ lc_tm_at 0 0 t2.
Proof. intros t1 t2 H. inversion H; subst; auto. Qed.

Lemma lc_abs_inv : forall T t, lc_tm_at 0 0 (tm_abs T t) ->
  lc_ty_at 0 T /\ lc_tm_at 0 1 t.
Proof. intros T t H. inversion H; subst; auto. Qed.

Lemma lc_tabs_inv : forall t, lc_tm_at 0 0 (tm_tabs t) -> lc_tm_at 1 0 t.
Proof. intros t H. inversion H; subst; auto. Qed.

Lemma lc_tapp_inv : forall t T, lc_tm_at 0 0 (tm_tapp t T) ->
  lc_tm_at 0 0 t /\ lc_ty_at 0 T.
Proof. intros t T H. inversion H; subst; auto. Qed.

Lemma lc_succ_inv : forall t, lc_tm_at 0 0 (tm_succ t) -> lc_tm_at 0 0 t.
Proof. intros t H. inversion H; subst; auto. Qed.

Lemma lc_natrec_inv : forall n b g, lc_tm_at 0 0 (tm_natrec n b g) ->
  lc_tm_at 0 0 n /\ lc_tm_at 0 0 b /\ lc_tm_at 0 0 g.
Proof. intros n b g H. inversion H; subst; auto. Qed.

(* ---------- Closedness is preserved by reduction ---------- *)

Lemma lc_step : forall t t', lc_tm_at 0 0 t -> step t t' -> lc_tm_at 0 0 t'.
Proof.
  intros t t' Hlc Hst. revert Hlc. induction Hst as
    [T body v Hlca Hv | t1 t1' t2 Hstep IH Hlc2 | v1 t2 t2' Hv Hstep IH
    | tb U Hlctabs Hlcty | t1 t1' U Hstep IH Hlcty | t1 t1' Hstep IH
    | n n' b g Hstep IH Hlcb Hlcg | n b b' g Hnum Hstep IH Hlcg
    | n b g g' Hnum Hvb Hstep IH | b g Hvb Hvg | n b g Hnum Hvb Hvg];
    intros Hlc; simpl in *.
  - apply lc_app_inv in Hlc. destruct Hlc as [Hlab Hlv].
    apply lc_abs_inv in Hlab. destruct Hlab as [Hty Hbody].
    apply lc_tm_at_open_tm_0 with (k := 0) (u := v).
    + assumption.
    + assumption.
  - apply lc_app_inv in Hlc. destruct Hlc as [Hl1 Hl2].
    apply lc_tm_app.
    + apply IH. assumption.
    + assumption.
  - apply lc_app_inv in Hlc. destruct Hlc as [Hl1 Hl2].
    apply lc_tm_app.
    + assumption.
    + apply IH. assumption.
  - apply lc_tapp_inv in Hlc. destruct Hlc as [Hlt Hlty].
    apply lc_tabs_inv in Hlt.
    apply lc_tm_at_open_ty_0 with (k := 0) (U := U).
    + assumption.
    + assumption.
  - apply lc_tapp_inv in Hlc. destruct Hlc as [Hlt Hlty].
    apply lc_tm_tapp.
    + apply IH. assumption.
    + assumption.
  - apply lc_succ_inv in Hlc. apply lc_tm_succ. apply IH. assumption.
  - apply lc_natrec_inv in Hlc. destruct Hlc as [Hln [Hlb Hlg]].
    apply lc_tm_rec.
    + apply IH. assumption.
    + assumption.
    + assumption.
  - apply lc_natrec_inv in Hlc. destruct Hlc as [Hln [Hlb Hlg]].
    apply lc_tm_rec.
    + assumption.
    + apply IH. assumption.
    + assumption.
  - apply lc_natrec_inv in Hlc. destruct Hlc as [Hln [Hlb Hlg]].
    apply lc_tm_rec.
    + assumption.
    + assumption.
    + apply IH. assumption.
  - apply lc_natrec_inv in Hlc. destruct Hlc as [Hln [Hlb Hlg]].
    assumption.
  - apply lc_natrec_inv in Hlc. destruct Hlc as [Hln [Hlb Hlg]].
    apply lc_succ_inv in Hln.
    apply lc_tm_app.
    + apply lc_tm_app; assumption.
    + apply lc_tm_rec; assumption.
Qed.

(* ---------- No free type atoms is preserved by reduction ---------- *)

Lemma no_ftv_app_inv : forall t1 t2, no_ftv_tm (tm_app t1 t2) ->
  no_ftv_tm t1 /\ no_ftv_tm t2.
Proof.
  intros t1 t2 H. simpl in *.
  split; intros X HX; apply (H X); simpl; rewrite in_app_iff; [left | right]; assumption.
Qed.

Lemma no_ftv_abs_inv : forall T t, no_ftv_tm (tm_abs T t) ->
  no_ftv_ty T /\ no_ftv_tm t.
Proof.
  intros T t H. simpl in *.
  split; intros X HX; apply (H X); simpl; rewrite in_app_iff; [left | right]; assumption.
Qed.

Lemma no_ftv_tabs_inv : forall t, no_ftv_tm (tm_tabs t) -> no_ftv_tm t.
Proof. intros t H. simpl in *. assumption. Qed.

Lemma no_ftv_tapp_inv : forall t T, no_ftv_tm (tm_tapp t T) ->
  no_ftv_tm t /\ no_ftv_ty T.
Proof.
  intros t T H. simpl in *.
  split; intros X HX; apply (H X); simpl; rewrite in_app_iff; [left | right]; assumption.
Qed.

Lemma no_ftv_succ_inv : forall t, no_ftv_tm (tm_succ t) -> no_ftv_tm t.
Proof. intros t H. simpl in *. assumption. Qed.

Lemma no_ftv_natrec_inv : forall n b g, no_ftv_tm (tm_natrec n b g) ->
  no_ftv_tm n /\ no_ftv_tm b /\ no_ftv_tm g.
Proof.
  intros n b g H. simpl in *. split.
  - intros X HX. apply (H X). simpl. rewrite in_app_iff. left. rewrite in_app_iff. left. assumption.
  - split.
    + intros X HX. apply (H X). simpl. rewrite in_app_iff. left. rewrite in_app_iff. right. assumption.
    + intros X HX. apply (H X). simpl. rewrite in_app_iff. right. assumption.
Qed.

Lemma no_ftv_app_intro : forall t1 t2, no_ftv_tm t1 -> no_ftv_tm t2 ->
  no_ftv_tm (tm_app t1 t2).
Proof.
  intros t1 t2 H1 H2 X HX. simpl in HX. rewrite in_app_iff in HX.
  destruct HX as [HX | HX]; [apply (H1 X) | apply (H2 X)]; assumption.
Qed.

Lemma no_ftv_tapp_intro : forall t T, no_ftv_tm t -> no_ftv_ty T ->
  no_ftv_tm (tm_tapp t T).
Proof.
  intros t T H1 H2 X HX. simpl in HX. rewrite in_app_iff in HX.
  destruct HX as [HX | HX]; [apply (H1 X) | apply (H2 X)]; assumption.
Qed.

Lemma no_ftv_succ_intro : forall t, no_ftv_tm t -> no_ftv_tm (tm_succ t).
Proof. intros t H X HX. simpl in HX. apply (H X). assumption. Qed.

Lemma no_ftv_natrec_intro : forall n b g, no_ftv_tm n -> no_ftv_tm b -> no_ftv_tm g ->
  no_ftv_tm (tm_natrec n b g).
Proof.
  intros n b g H1 H2 H3 X HX. simpl in HX. repeat rewrite in_app_iff in HX.
  destruct HX as [[HX | HX] | HX].
  - apply (H1 X). assumption.
  - apply (H2 X). assumption.
  - apply (H3 X). assumption.
Qed.

Lemma ftv_step : forall t t', no_ftv_tm t -> step t t' -> no_ftv_tm t'.
Proof.
  intros t t' Hn Hst. revert Hn. induction Hst as
    [T body v Hlca Hv | t1 t1' t2 Hstep IH Hlc2 | v1 t2 t2' Hv Hstep IH
    | tb U Hlctabs Hlcty | t1 t1' U Hstep IH Hlcty | t1 t1' Hstep IH
    | n n' b g Hstep IH Hlcb Hlcg | n b b' g Hnum Hstep IH Hlcg
    | n b g g' Hnum Hvb Hstep IH | b g Hvb Hvg | n b g Hnum Hvb Hvg];
    intros Hn; simpl in *.
  - apply no_ftv_app_inv in Hn. destruct Hn as [Hnab Hnv].
    apply no_ftv_abs_inv in Hnab. destruct Hnab as [Hnt Hnb].
    intros X HX. apply in_ftv_tm_open_tm_rec in HX.
    destruct HX as [HX | HX].
    + apply (Hnb X). assumption.
    + apply (Hnv X). assumption.
  - apply no_ftv_app_inv in Hn. destruct Hn as [Hn1 Hn2].
    apply no_ftv_app_intro.
    + apply IH. assumption.
    + assumption.
  - apply no_ftv_app_inv in Hn. destruct Hn as [Hn1 Hn2].
    apply no_ftv_app_intro.
    + assumption.
    + apply IH. assumption.
  - apply no_ftv_tapp_inv in Hn. destruct Hn as [Hnt HnU].
    apply no_ftv_tabs_inv in Hnt.
    intros X HX. apply in_ftv_tm_open_tm_ty_rec in HX.
    destruct HX as [HX | HX].
    + apply (Hnt X). assumption.
    + apply (HnU X). assumption.
  - apply no_ftv_tapp_inv in Hn. destruct Hn as [Hnt HnU].
    apply no_ftv_tapp_intro.
    + apply IH. assumption.
    + assumption.
  - apply no_ftv_succ_inv in Hn. apply no_ftv_succ_intro. apply IH. assumption.
  - apply no_ftv_natrec_inv in Hn. destruct Hn as [Hnn [Hnb Hng]].
    apply no_ftv_natrec_intro.
    + apply IH. assumption.
    + assumption.
    + assumption.
  - apply no_ftv_natrec_inv in Hn. destruct Hn as [Hnn [Hnb Hng]].
    apply no_ftv_natrec_intro.
    + assumption.
    + apply IH. assumption.
    + assumption.
  - apply no_ftv_natrec_inv in Hn. destruct Hn as [Hnn [Hnb Hng]].
    apply no_ftv_natrec_intro.
    + assumption.
    + assumption.
    + apply IH. assumption.
  - apply no_ftv_natrec_inv in Hn. destruct Hn as [Hnn [Hnb Hng]].
    assumption.
  - apply no_ftv_natrec_inv in Hn. destruct Hn as [Hnn [Hnb Hng]].
    intros X HX. simpl in HX. repeat rewrite in_app_iff in HX.
    destruct HX as [[HX | HX] | HX].
    + apply (Hng X). assumption.
    + apply (Hnn X). assumption.
    + destruct HX as [HX | HX].
      * destruct HX as [HX | HX].
        -- apply (Hnn X). assumption.
        -- apply (Hnb X). assumption.
      * apply (Hng X). assumption.
Qed.

Lemma closed_step : forall t t', closed_tm t -> step t t' -> closed_tm t'.
Proof.
  intros t t' [Hlc Hnf] Hst. split.
  - eapply lc_step; eauto.
  - eapply ftv_step; eauto.
Qed.

(* ---------- Freshness helpers ---------- *)

Lemma fresh_notin_app_l : forall l1 l2, ~ In (fresh_atom (l1 ++ l2)) l1.
Proof.
  intros l1 l2 H. apply (fresh_atom_notin (l1 ++ l2)). apply in_or_app. left. assumption.
Qed.

Lemma fresh_notin_app_r : forall l1 l2, ~ In (fresh_atom (l1 ++ l2)) l2.
Proof.
  intros l1 l2 H. apply (fresh_atom_notin (l1 ++ l2)). apply in_or_app. right. assumption.
Qed.

(* ---------- Well-formed types are locally closed ---------- *)

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> lc_ty_at 0 T.
Proof.
  intros Delta T H. induction H as
    [Delta0 X Hin | Delta0 T1 T2 H1 IH1 H2 IH2 | L Delta0 T0 Hsub IH | Delta0].
  - apply lc_ty_fvar.
  - apply lc_ty_arrow; assumption.
  - apply lc_ty_all.
    pose proof (IH (fresh_atom L) (fresh_atom_notin L)) as Hx.
    apply lc_ty_at_open_inv with (j := 0) (U := Ty_FVar (fresh_atom L)).
    exact Hx.
  - apply lc_ty_nat.
Qed.

Lemma wf_ty_ftv : forall Delta T, wf_ty Delta T ->
  forall X, In X (ftv_ty T) -> In X Delta.
Proof.
  intros Delta T H. induction H as
    [Delta0 X Hin | Delta0 T1 T2 H1 IH1 H2 IH2 | L Delta0 T0 Hsub IH | Delta0].
  - intros Y HY. simpl in HY. destruct HY as [-> | Hf]; [assumption | destruct Hf].
  - intros Y HY. simpl in HY. rewrite in_app_iff in HY.
    destruct HY as [HY | HY]; [apply IH1 | apply IH2]; assumption.
  - intros Y HY. simpl in HY.
    assert (HX0L : ~ In (fresh_atom (L ++ ftv_ty T0)) L) by apply fresh_notin_app_l.
    assert (HX0T : ~ In (fresh_atom (L ++ ftv_ty T0)) (ftv_ty T0)) by apply fresh_notin_app_r.
    assert (HY' : In Y (ftv_ty (open_ty_rec 0 (Ty_FVar (fresh_atom (L ++ ftv_ty T0))) T0))).
    { apply ftv_ty_subset_open_ty_rec. assumption. }
    pose proof (IH (fresh_atom (L ++ ftv_ty T0)) HX0L Y HY') as Hres.
    destruct Hres as [Heq | Hin].
    + exfalso. apply HX0T. rewrite Heq. assumption.
    + assumption.
  - intros Y HY. simpl in HY. destruct HY.
Qed.

(* ---------- Well-typed terms: local closure and free type atoms ---------- *)

Lemma has_type_inv : forall Delta Gamma t T, has_type Delta Gamma t T ->
  lc_tm_at 0 0 t /\
  (forall X, In X (ftv_tm t) -> In X Delta) /\
  (forall X, In X (ftv_ty T) -> In X Delta).
Proof.
  intros Delta Gamma t T H. induction H as
    [Delta0 Gamma0 x T0 Hlook Hwf
    | L Delta0 Gamma0 T1 t2 T2 Hwf Hbody IHbody
    | Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta0 Gamma0 t0 T0 Hbody IHbody
    | Delta0 Gamma0 t0 T0 U H1 IH1 HwfU
    | Delta0 Gamma0
    | Delta0 Gamma0 n Hn IHn
    | Delta0 Gamma0 n b g T0 Hn IHn Hb IHb Hg IHg].
  - split.
    + apply lc_tm_fvar.
    + split.
      * intros X HX. simpl in HX. destruct HX.
      * intros X HX. eapply wf_ty_ftv; eauto.
  - pose proof (IHbody (fresh_atom (L ++ fvars_tm t2))
                       (fresh_notin_app_l L (fvars_tm t2))) as HIHx.
    destruct HIHx as [Hlcx [Hftvx HftvT2]].
    split.
    + apply lc_tm_abs.
      * exact (wf_ty_lc Delta0 T1 Hwf).
      * apply lc_tm_at_open_tm_inv with (k := 0)
          (u := tm_fvar (fresh_atom (L ++ fvars_tm t2))).
        exact Hlcx.
    + split.
      * intros X HX. simpl in HX. rewrite in_app_iff in HX.
        destruct HX as [HX | HX].
        -- eapply wf_ty_ftv; eauto.
        -- apply (Hftvx X). apply ftv_tm_subset_open_tm_rec
             with (k := 0) (u := tm_fvar (fresh_atom (L ++ fvars_tm t2))).
           exact HX.
      * intros X HX. simpl in HX. rewrite in_app_iff in HX.
        destruct HX as [HX | HX].
        -- eapply wf_ty_ftv; eauto.
        -- apply (HftvT2 X). exact HX.
  - destruct IH1 as [Hlc1 [Hftv1 HftvT1]].
    destruct IH2 as [Hlc2 [Hftv2 HftvT2]].
    split.
    + apply lc_tm_app; assumption.
    + split.
      * intros X HX. simpl in HX. rewrite in_app_iff in HX.
        destruct HX as [HX | HX]; [apply (Hftv1 X) | apply (Hftv2 X)]; assumption.
      * intros X HX. apply (HftvT1 X). simpl. rewrite in_app_iff. right. assumption.
  - pose proof (IHbody (fresh_atom (L ++ (ftv_tm t0 ++ ftv_ty T0)))
                       (fresh_notin_app_l L (ftv_tm t0 ++ ftv_ty T0))) as HIHx.
    destruct HIHx as [Hlcx [Hftvx HftvT]].
    assert (HX0t : ~ In (fresh_atom (L ++ (ftv_tm t0 ++ ftv_ty T0))) (ftv_tm t0)).
    { intro Hc. apply (fresh_notin_app_r L (ftv_tm t0 ++ ftv_ty T0)).
      rewrite in_app_iff. left. assumption. }
    assert (HX0T : ~ In (fresh_atom (L ++ (ftv_tm t0 ++ ftv_ty T0))) (ftv_ty T0)).
    { intro Hc. apply (fresh_notin_app_r L (ftv_tm t0 ++ ftv_ty T0)).
      rewrite in_app_iff. right. assumption. }
    split.
    + apply lc_tm_tabs.
      apply lc_tm_at_open_ty_inv with (j := 0) (k := 0)
        (U := Ty_FVar (fresh_atom (L ++ (ftv_tm t0 ++ ftv_ty T0)))).
      exact Hlcx.
    + split.
      * intros X HX.
        assert (HX' : In X (ftv_tm (open_tm_ty_rec 0
                       (Ty_FVar (fresh_atom (L ++ (ftv_tm t0 ++ ftv_ty T0)))) t0))).
        { apply ftv_tm_subset_open_tm_ty_rec. exact HX. }
        pose proof (Hftvx X HX') as Hres.
        destruct Hres as [Heq | Hin].
        -- exfalso. apply HX0t. subst X. exact HX.
        -- assumption.
      * intros X HX.
        assert (HX' : In X (ftv_ty (open_ty_rec 0
                       (Ty_FVar (fresh_atom (L ++ (ftv_tm t0 ++ ftv_ty T0)))) T0))).
        { apply ftv_ty_subset_open_ty_rec. exact HX. }
        pose proof (HftvT X HX') as Hres.
        destruct Hres as [Heq | Hin].
        -- exfalso. apply HX0T. subst X. exact HX.
        -- assumption.
  - destruct IH1 as [Hlc1 [Hftv1 HftvT1]].
    split.
    + apply lc_tm_tapp.
      * assumption.
      * exact (wf_ty_lc Delta0 U HwfU).
    + split.
      * intros X HX. simpl in HX. rewrite in_app_iff in HX.
        destruct HX as [HX | HX].
        -- apply (Hftv1 X). assumption.
        -- eapply wf_ty_ftv; eauto.
      * intros X HX.
        apply in_ftv_ty_open_ty_rec in HX. destruct HX as [HX | HX].
        -- apply (HftvT1 X). simpl. assumption.
        -- eapply wf_ty_ftv; eauto.
  - split.
    + apply lc_tm_zero.
    + split; intros X HX; simpl in HX; destruct HX.
  - destruct IHn as [Hlc [Hftv HftvNat]].
    split.
    + apply lc_tm_succ. assumption.
    + split.
      * intros X HX. simpl in HX. apply (Hftv X). assumption.
      * intros X HX. simpl in HX. destruct HX.
  - destruct IHn as [Hlcn [Hftvn HftvNat]].
    destruct IHb as [Hlcb [Hftvb HftvT]].
    destruct IHg as [Hlcs [Hftvs HftvS]].
    split.
    + apply lc_tm_rec; assumption.
    + split.
      * intros X HX. simpl in HX. repeat rewrite in_app_iff in HX.
        destruct HX as [[HX | HX] | HX];
          [apply (Hftvn X) | apply (Hftvb X) | apply (Hftvs X)]; assumption.
      * intros X HX. apply (HftvT X). assumption.
Qed.

(* ================================================================ *)
(* Level-indexed approximation of the logical relation              *)
(* ================================================================ *)

Fixpoint LR (n : nat) (T : ty) (t : tm) : Prop :=
  match n with
  | 0 => True
  | S n' =>
      match T with
      | Ty_Nat => strongly_normalizing t
      | Ty_Arrow A B =>
          strongly_normalizing t /\ forall u, closed_tm u -> LR n' A u -> LR n' B (tm_app t u)
      | Ty_All A =>
          strongly_normalizing t /\ forall U, closed_ty U -> LR n' (open_ty A U) (tm_tapp t U)
      | _ => strongly_normalizing t
      end
  end.

Lemma not_value_app : forall t1 t2, ~ value (tm_app t1 t2).
Proof.
  intros t1 t2 H. inversion H; subst.
  match goal with Hn : numeric_value (tm_app t1 t2) |- _ => inversion Hn end.
Qed.

Lemma not_value_tapp : forall t U, ~ value (tm_tapp t U).
Proof.
  intros t U H. inversion H; subst.
  match goal with Hn : numeric_value (tm_tapp t U) |- _ => inversion Hn end.
Qed.

Lemma not_value_natrec : forall n b s, ~ value (tm_natrec n b s).
Proof.
  intros n b s H. inversion H; subst.
  match goal with Hn : numeric_value (tm_natrec n b s) |- _ => inversion Hn end.
Qed.

Lemma LR_sn : forall n T t, LR (S n) T t -> strongly_normalizing t.
Proof.
  intros n T t H. destruct T; simpl in *; tauto.
Qed.

Lemma LR_step : forall n T t t', LR n T t -> step t t' -> LR n T t'.
Proof.
  induction n as [| n IH]; intros T t t' H Hst.
  - simpl in *. exact I.
  - destruct T as [i | X | A B | A | ]; simpl in *.
    + inversion H; eauto.
    + inversion H; eauto.
    + destruct H as [Hsn Hcl]. split.
      * inversion Hsn; eauto.
      * intros u Hu HA. apply (IH B (tm_app t u) (tm_app t' u)).
        -- apply Hcl; assumption.
        -- apply ST_App1; [exact Hst | exact (proj1 Hu)].
    + destruct H as [Hsn Hcl]. split.
      * inversion Hsn; eauto.
      * intros U HU. apply (IH (open_ty A U) (tm_tapp t U) (tm_tapp t' U)).
        -- apply Hcl; assumption.
        -- apply ST_TApp; [exact Hst | exact (proj1 HU)].
    + inversion H; eauto.
Qed.

Lemma LR_expand : forall n T t,
  ~ value t -> (forall t', step t t' -> LR n T t') -> LR n T t.
Proof.
  induction n as [| n IH]; intros T t Hnv Hred.
  - simpl. exact I.
  - destruct T as [i | X | A B | A | ]; simpl in *.
    + apply SN_intro. intros u Hu. apply Hred. assumption.
    + apply SN_intro. intros u Hu. apply Hred. assumption.
    + split.
      * apply SN_intro. intros u Hu. apply (proj1 (Hred u Hu)).
      * intros u Hu HA. apply (IH B (tm_app t u)).
        -- apply not_value_app.
        -- intros r Hst. inversion Hst; subst.
           ++ exfalso. apply Hnv. apply v_abs. assumption.
           ++ match goal with Hst1 : t --> ?xx |- LR n B (tm_app ?xx u) =>
                pose proof (Hred xx Hst1) as Ht'; simpl in Ht';
                apply (proj2 Ht' u Hu HA) end.
           ++ exfalso. apply Hnv. assumption.
    + split.
      * apply SN_intro. intros u Hu. apply (proj1 (Hred u Hu)).
      * intros U HU. apply (IH (open_ty A U) (tm_tapp t U)).
        -- apply not_value_tapp.
        -- intros r Hst. inversion Hst; subst.
           ++ exfalso. apply Hnv. apply v_tabs. assumption.
           ++ match goal with Hst1 : t --> ?xx |- LR n (open_ty A U) (tm_tapp ?xx U) =>
                pose proof (Hred xx Hst1) as Ht'; simpl in Ht';
                apply (proj2 Ht' U HU) end.
    + apply SN_intro. intros u Hu. apply Hred. assumption.
Qed.

Lemma LR_app : forall n A B t1 t2,
  LR (S n) (Ty_Arrow A B) t1 -> closed_tm t2 -> LR n A t2 ->
  LR n B (tm_app t1 t2).
Proof.
  intros n A B t1 t2 H Hc H2. simpl in H.
  destruct H as [Hsn Hcl]. apply (Hcl t2 Hc H2).
Qed.

Lemma LR_tapp : forall n A t U,
  LR (S n) (Ty_All A) t -> closed_ty U ->
  LR n (open_ty A U) (tm_tapp t U).
Proof.
  intros n A t U H HU. simpl in H. destruct H as [Hsn Hcl]. apply (Hcl U HU).
Qed.

Lemma LR_abs_app : forall n A B body,
  (forall u, closed_tm u -> LR n A u -> LR n B (open_tm body u)) ->
  forall u, strongly_normalizing u -> closed_tm u -> LR n A u ->
  LR n B (tm_app (tm_abs A body) u).
Proof.
  intros n A B body Hbody u Hsn. induction Hsn as [u Hred IH].
  intros Hcl Hu.
  assert (Hred' : forall r, step (tm_app (tm_abs A body) u) r -> LR n B r).
  { intros r Hst. inversion Hst; subst.
    - apply Hbody; assumption.
    - match goal with H : step (tm_abs A body) _ |- _ => inversion H end.
    - apply IH.
      + assumption.
      + apply closed_step with (t := u); assumption.
      + eapply LR_step; eassumption. }
  apply LR_expand with (t := tm_app (tm_abs A body) u).
  - apply not_value_app.
  - exact Hred'.
Qed.

Lemma LR_abs : forall n A B body,
  locally_closed_tm (tm_abs A body) ->
  (forall u, closed_tm u -> LR n A u -> LR n B (open_tm body u)) ->
  LR (S n) (Ty_Arrow A B) (tm_abs A body).
Proof.
  intros n A B body Hlc Hbody. simpl. split.
  - apply sn_value. apply v_abs. assumption.
  - intros u Hcl Hu.
    destruct n as [| m]; [simpl; exact I | ].
    eapply LR_abs_app.
    + exact Hbody.
    + apply LR_sn with (n := m) (T := A). assumption.
    + exact Hcl.
    + exact Hu.
Qed.

Lemma LR_tabs : forall n A body,
  locally_closed_tm (tm_tabs body) ->
  (forall U, closed_ty U -> LR n (open_ty A U) (open_tm_ty body U)) ->
  LR (S n) (Ty_All A) (tm_tabs body).
Proof.
  intros n A body Hlc Hbody. simpl. split.
  - apply sn_value. apply v_tabs. assumption.
  - intros U HU.
    destruct n as [| m]; [simpl; exact I | ].
    apply LR_expand with (t := tm_tapp (tm_tabs body) U).
    + apply not_value_tapp.
    + intros r Hst. inversion Hst; subst.
      * apply Hbody; assumption.
      * match goal with H : step (tm_tabs body) _ |- _ => inversion H end.
Qed.

Lemma sn_succ : forall t, strongly_normalizing t -> strongly_normalizing (tm_succ t).
Proof.
  intros t H. induction H as [t Hred IH].
  apply SN_intro. intros u Hu. inversion Hu; subst.
  match goal with Hst : step t ?t' |- strongly_normalizing (tm_succ ?t') =>
    apply (IH t' Hst) end.
Qed.

Lemma numeric_value_numeral : forall n, numeric_value n -> exists k, n = numeral k.
Proof.
  intros n H. induction H as [| m Hm [k Hk]].
  - exists 0. reflexivity.
  - exists (S k). simpl. rewrite <- Hk. reflexivity.
Qed.

Lemma numeral_numeric : forall k, numeric_value (numeral k).
Proof. induction k; simpl; [constructor | apply nv_succ; assumption]. Qed.

Lemma numeral_no_ftv : forall k, no_ftv_tm (numeral k).
Proof.
  induction k; simpl.
  - intros X HX. destruct HX.
  - intros X HX. simpl in HX. apply (IHk X HX).
Qed.

Lemma numeral_closed : forall k, closed_tm (numeral k).
Proof.
  intros k. split; [apply numeric_value_lc, numeral_numeric | apply numeral_no_ftv].
Qed.

Lemma LR_numeral : forall k n, LR (S n) Ty_Nat (numeral k).
Proof.
  intros k n. simpl. apply sn_value. apply v_nat. apply numeral_numeric.
Qed.

Lemma LR_zero : forall n, LR n Ty_Nat tm_zero.
Proof. intros n. destruct n; simpl; [exact I | apply sn_value; apply v_nat; constructor]. Qed.

Lemma LR_succ : forall n t, LR (S n) Ty_Nat t -> LR (S n) Ty_Nat (tm_succ t).
Proof. intros n t H. simpl in *. apply sn_succ. exact H. Qed.

(* ---------- Primitive recursion ---------- *)

Lemma LR_natrec_numeral : forall k,
  forall n T b, strongly_normalizing b -> LR (S n) T b ->
  forall s, strongly_normalizing s ->
  LR (S (S (S n))) (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  closed_tm b -> closed_tm s ->
  LR (S n) T (tm_natrec (numeral k) b s).
Proof.
  induction k as [| k IHk]; intros n T b Hsnb.
  - revert n T. induction Hsnb as [b Hredb IHb].
    intros n T Hb s Hsns Hs Hcb Hcs.
    revert Hb Hs Hcb Hcs. induction Hsns as [s Hreds IHs]. intros Hb Hs Hcb Hcs.
    assert (Hsns : strongly_normalizing s) by (apply SN_intro; exact Hreds).
    apply LR_expand with (t := tm_natrec tm_zero b s).
    + apply not_value_natrec.
    + intros r Hst. inversion Hst; subst.
      * exfalso. eapply numeric_value_no_step; [apply nv_zero | eassumption].
      * eapply IHb; eauto using LR_step, closed_step.
      * eapply IHs; eauto using LR_step, closed_step.
      * exact Hb.
  - revert n T. induction Hsnb as [b Hredb IHb].
    intros n T Hb s Hsns Hs Hcb Hcs.
    revert Hb Hs Hcb Hcs. induction Hsns as [s Hreds IHs]. intros Hb Hs Hcb Hcs.
    assert (Hsns : strongly_normalizing s) by (apply SN_intro; exact Hreds).
    apply LR_expand with (t := tm_natrec (tm_succ (numeral k)) b s).
    + apply not_value_natrec.
    + intros r Hst. inversion Hst; subst.
      * exfalso. eapply numeric_value_no_step;
          [apply nv_succ, numeral_numeric | eassumption].
      * eapply IHb; eauto using LR_step, closed_step.
      * eapply IHs; eauto using LR_step, closed_step.
      * eapply LR_app.
        -- eapply LR_app; [ exact Hs | apply numeral_closed | apply LR_numeral ].
        -- split.
           ++ apply lc_tm_rec; [ apply (proj1 (numeral_closed k)) | exact (proj1 Hcb) | exact (proj1 Hcs) ].
           ++ apply no_ftv_natrec_intro;
                [ apply numeral_no_ftv | exact (proj2 Hcb) | exact (proj2 Hcs) ].
        -- eapply IHk; eauto using LR_step, LR_sn.
Qed.

Lemma LR_natrec : forall n0,
  strongly_normalizing n0 ->
  forall n T b s,
  LR (S n) Ty_Nat n0 ->
  LR (S n) T b ->
  LR (S (S (S n))) (Ty_Arrow Ty_Nat (Ty_Arrow T T)) s ->
  closed_tm b -> closed_tm s ->
  LR (S n) T (tm_natrec n0 b s).
Proof.
  intros n0 Hsn. induction Hsn as [n0 Hred IH].
  intros n T b s Hn Hb Hs Hcb Hcs.
  apply LR_expand with (t := tm_natrec n0 b s).
  - apply not_value_natrec.
  - intros r Hst. inversion Hst; subst.
    + eapply IH; eauto using LR_step.
    + match goal with Hnum : numeric_value ?x |- _ =>
        destruct (numeric_value_numeral x Hnum) as [kk Hkk]; subst x end.
      eapply LR_natrec_numeral; eauto using LR_step, LR_sn, closed_step.
    + match goal with Hnum : numeric_value ?x |- _ =>
        destruct (numeric_value_numeral x Hnum) as [kk Hkk]; subst x end.
      eapply LR_natrec_numeral; eauto using LR_step, LR_sn, closed_step.
    + exact Hb.
    + match goal with Hnum : numeric_value ?x |- _ =>
        destruct (numeric_value_numeral x Hnum) as [kk Hkk]; subst x end.
      eapply LR_app.
      * eapply LR_app; [ exact Hs | apply numeral_closed | apply LR_numeral ].
      * split.
        ++ apply lc_tm_rec; [ apply (proj1 (numeral_closed kk)) | exact (proj1 Hcb) | exact (proj1 Hcs) ].
        ++ apply no_ftv_natrec_intro;
             [ apply numeral_no_ftv | exact (proj2 Hcb) | exact (proj2 Hcs) ].
      * eapply LR_natrec_numeral; eauto using LR_step, LR_sn, closed_step.
Qed.

(* ---------- Auxiliary substitution lemmas for the fundamental theorem ---------- *)

Definition ctx_ftv (Gamma : context) : list atom :=
  flat_map (fun p => ftv_ty (snd p)) Gamma.

Lemma ty_subst_env_id : forall sT T, no_ftv_ty T -> ty_subst_env sT T = T.
Proof.
  intros sT. fix IH 1. intros T. destruct T as [i | X | T1 T2 | T1 | ]; intros H; simpl in *.
  - reflexivity.
  - exfalso. apply (H X). simpl. auto.
  - assert (H1 : no_ftv_ty T1).
    { intro Y. intro HY. apply (H Y). simpl. rewrite in_app_iff. left. exact HY. }
    assert (H2 : no_ftv_ty T2).
    { intro Y. intro HY. apply (H Y). simpl. rewrite in_app_iff. right. exact HY. }
    f_equal. apply (IH T1 H1). apply (IH T2 H2).
  - assert (H1 : no_ftv_ty T1).
    { intro Y. intro HY. apply (H Y). simpl. exact HY. }
    f_equal. apply (IH T1 H1).
  - reflexivity.
Qed.

Lemma tm_subst_env_id : forall sT t,
  no_ftv_tm t -> tm_subst_env sT (fun x => tm_fvar x) t = t.
Proof.
  intros sT. fix IH 1. intros t. destruct t as [i | x | A b | a b | b | b A | | b | n b g];
    intros H; simpl in *.
  - reflexivity.
  - reflexivity.
  - assert (HA : no_ftv_ty A).
    { intro Y. intro HY. apply (H Y). simpl. rewrite in_app_iff. left. exact HY. }
    assert (Hb : no_ftv_tm b).
    { intro Y. intro HY. apply (H Y). simpl. rewrite in_app_iff. right. exact HY. }
    rewrite (ty_subst_env_id sT A HA), (IH b Hb). reflexivity.
  - assert (Ha : no_ftv_tm a).
    { intro Y. intro HY. apply (H Y). simpl. rewrite in_app_iff. left. exact HY. }
    assert (Hb : no_ftv_tm b).
    { intro Y. intro HY. apply (H Y). simpl. rewrite in_app_iff. right. exact HY. }
    rewrite (IH a Ha), (IH b Hb). reflexivity.
  - rewrite (IH b). reflexivity. intro Y. intro HY. apply (H Y). simpl. exact HY.
  - assert (Hb : no_ftv_tm b).
    { intro Y. intro HY. apply (H Y). simpl. rewrite in_app_iff. left. exact HY. }
    assert (HA : no_ftv_ty A).
    { intro Y. intro HY. apply (H Y). simpl. rewrite in_app_iff. right. exact HY. }
    rewrite (IH b Hb), (ty_subst_env_id sT A HA). reflexivity.
  - reflexivity.
  - rewrite (IH b). reflexivity. intro Y. intro HY. apply (H Y). simpl. exact HY.
  - assert (Hn : no_ftv_tm n).
    { intro Y. intro HY. apply (H Y). simpl. repeat rewrite in_app_iff. left. left. exact HY. }
    assert (Hb : no_ftv_tm b).
    { intro Y. intro HY. apply (H Y). simpl. repeat rewrite in_app_iff. left. right. exact HY. }
    assert (Hg : no_ftv_tm g).
    { intro Y. intro HY. apply (H Y). simpl. repeat rewrite in_app_iff. right. exact HY. }
    rewrite (IH n Hn), (IH b Hb), (IH g Hg). reflexivity.
Qed.

Lemma closed_subst_ty : forall sT T,
  (forall X, closed_ty (sT X)) -> lc_ty_at 0 T ->
  closed_ty (ty_subst_env sT T).
Proof.
  intros sT T Hc Hlc. split.
  - apply ty_subst_env_lc with (K := 0); [assumption | intro X; apply (proj1 (Hc X))].
  - apply ty_subst_env_no_ftv. intro X. apply (proj2 (Hc X)).
Qed.

Lemma closed_subst_tm : forall sT s t,
  (forall X, closed_ty (sT X)) -> (forall x, closed_tm (s x)) ->
  lc_tm_at 0 0 t ->
  closed_tm (tm_subst_env sT s t).
Proof.
  intros sT s t HcT Hc Hlc. split.
  - apply tm_subst_env_lc with (K := 0) (k := 0);
      [assumption | intro X; apply (proj1 (HcT X)) | intro x; apply (proj1 (Hc x))].
  - apply tm_subst_env_no_ftv.
    + intro X. apply (proj2 (HcT X)).
    + intro x. apply (proj2 (Hc x)).
Qed.

Lemma subst_extend_open : forall sT s x u t,
  (forall y, lc_tm_at 0 0 (extend_tm s x u y)) ->
  ~ In x (fvars_tm t) ->
  tm_subst_env sT (extend_tm s x u) (open_tm t (tm_fvar x)) =
  open_tm (tm_subst_env sT s t) u.
Proof.
  intros sT s x u t Hlc Hfresh.
  unfold open_tm.
  rewrite (tm_subst_env_open_tm_rec sT (extend_tm s x u) 0 (tm_fvar x) t Hlc).
  assert (He : tm_subst_env sT (extend_tm s x u) (tm_fvar x) = u).
  { simpl. apply extend_tm_eq. }
  rewrite He.
  assert (Ha : tm_subst_env sT (extend_tm s x u) t = tm_subst_env sT s t).
  { apply tm_subst_env_agree. intros y Hy.
    destruct (Nat.eqb y x) eqn:E.
    - apply eqb_true_eq in E. subst y. exfalso. apply Hfresh. exact Hy.
    - apply extend_tm_neq. apply eqb_false_neq. exact E. }
  rewrite Ha. reflexivity.
Qed.

Lemma subst_extend_open_ty : forall sT s x u t,
  (forall Y, lc_ty_at 0 (sT Y)) -> (forall y, lc_tm_at 0 0 (s y)) ->
  ~ In x (ftv_tm t) ->
  tm_subst_env (extend_ty sT x u) s (open_tm_ty t (Ty_FVar x)) =
  open_tm_ty (tm_subst_env sT s t) u.
Proof.
  intros sT s x u t HT Hs Hfresh.
  unfold open_tm_ty.
  rewrite (tm_subst_env_open_tm_ty_FVar sT s x u 0 t HT Hs Hfresh).
  reflexivity.
Qed.

(* ---------- The fundamental theorem ---------- *)

Lemma fundamental : forall Delta Gamma t T, has_type Delta Gamma t T ->
  forall n sT s,
  (forall X, closed_ty (sT X)) ->
  (forall x, closed_tm (s x)) ->
  (forall k x U, lookup_context x Gamma = Some U -> LR k (ty_subst_env sT U) (s x)) ->
  LR n (ty_subst_env sT T) (tm_subst_env sT s t).
Proof.
  intros Delta Gamma t T H. induction H as
    [ Delta0 Gamma0 x T0 Hlook Hwf
    | L Delta0 Gamma0 T1 t2 T2 Hwf Hbody IHbody
    | Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
    | L Delta0 Gamma0 t0 T0 Hbody IHbody
    | Delta0 Gamma0 t0 T0 U H1 IH1 HwfU
    | Delta0 Gamma0
    | Delta0 Gamma0 n0 Hn IHn
    | Delta0 Gamma0 n0 b g T0 Hn IHn Hb IHb Hg IHg ];
    intros n sT s HcT Hc Hsat.
  - simpl. apply (Hsat n). exact Hlook.
  - destruct n as [| m].
    + simpl. exact I.
    + simpl. apply LR_abs.
      * apply lc_tm_abs.
        -- apply (proj1 (closed_subst_ty sT T1 HcT (wf_ty_lc Delta0 T1 Hwf))).
        -- apply tm_subst_env_lc with (K := 0) (k := 1).
           ++ apply lc_tm_at_open_tm_inv with (k := 0)
                (u := tm_fvar (fresh_atom (L ++ fvars_tm t2))).
              apply (proj1 (has_type_inv _ _ _ _
                (Hbody (fresh_atom (L ++ fvars_tm t2)) (fresh_notin_app_l L (fvars_tm t2))))).
           ++ intro X. apply (proj1 (HcT X)).
           ++ intro y. apply (proj1 (Hc y)).
      * intros u Hclu Hu.
        set (x0 := fresh_atom (L ++ (fvars_tm t2 ++ ctx_ftv Gamma0))).
        assert (Hx0L : ~ In x0 L).
        { subst x0. apply fresh_notin_app_l. }
        assert (Hx0F : ~ In x0 (fvars_tm t2)).
        { subst x0. intro Hc0. apply (fresh_notin_app_r L (fvars_tm t2 ++ ctx_ftv Gamma0)).
          rewrite in_app_iff. left. exact Hc0. }
        assert (Hx0G : ~ In x0 (ctx_ftv Gamma0)).
        { subst x0. intro Hc0. apply (fresh_notin_app_r L (fvars_tm t2 ++ ctx_ftv Gamma0)).
          rewrite in_app_iff. right. exact Hc0. }
        assert (Hcl : forall y, closed_tm (extend_tm s x0 u y)).
        { intro y. destruct (Nat.eqb y x0) eqn:E.
          - apply eqb_true_eq in E. subst y. rewrite (extend_tm_eq s x0 u). exact Hclu.
          - apply eqb_false_neq in E. rewrite (extend_tm_neq s x0 u y E). apply Hc. }
        assert (Hsat' : forall y U', lookup_context y ((x0, T1) :: Gamma0) = Some U' ->
                         LR m (ty_subst_env sT U') (extend_tm s x0 u y)).
        { intros y U' Hlook. destruct (Nat.eqb y x0) eqn:E.
          - apply eqb_true_eq in E. subst y. rewrite (extend_tm_eq s x0 u).
            simpl in Hlook. rewrite Nat.eqb_refl in Hlook. injection Hlook as ->. exact Hu.
          - rewrite (extend_tm_neq s x0 u y (eqb_false_neq _ _ E)).
            apply (Hsat m y U'). simpl in Hlook. rewrite E in Hlook. exact Hlook. }
        specialize (IHbody x0 Hx0L m sT (extend_tm s x0 u) HcT Hcl Hsat').
        rewrite (subst_extend_open sT s x0 u t2 (fun y => proj1 (Hcl y)) Hx0F) in IHbody.
        exact IHbody.
  - destruct n as [| m].
    + simpl. exact I.
    + simpl. eapply LR_app.
      * eapply IH1; eauto.
      * apply closed_subst_tm; [ exact HcT | exact Hc | apply (proj1 (has_type_inv _ _ _ _ H2)) ].
      * eapply IH2; eauto.
  - destruct n as [| m].
    + simpl. exact I.
    + simpl.
      assert (Hclosed : closed_ty (ty_subst_env sT U)).
      { apply closed_subst_ty; [ exact HcT | apply wf_ty_lc; exact HwfU ]. }
      assert (Hrw : ty_subst_env sT (open_ty T0 U) = open_ty (ty_subst_env sT T0) (ty_subst_env sT U)).
      { apply ty_subst_env_open_ty_rec. intro X. apply (proj1 (HcT X)). }
      rewrite Hrw.
      eapply LR_tapp.
      * eapply IH1; eauto.
      * exact Hclosed.
  - apply LR_zero.
  - destruct n as [| m].
    + simpl. exact I.
    + simpl. apply LR_succ. exact IHn.
  - destruct n as [| m].
    + simpl. exact I.
    + simpl. eapply LR_natrec.
      * eapply IHn; eauto.
      * eapply IHb; eauto.
      * eapply IHg; eauto.
      * apply closed_subst_tm; [ exact HcT | exact Hc | apply (proj1 (has_type_inv _ _ _ _ Hb)) ].
      * apply closed_subst_tm; [ exact HcT | exact Hc | apply (proj1 (has_type_inv _ _ _ _ Hg)) ].
Qed.

(* Construct the logical relation and supporting proofs here. *)

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationRecursionHardTask.
