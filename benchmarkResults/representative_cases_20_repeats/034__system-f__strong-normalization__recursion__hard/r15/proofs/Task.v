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

(* ---------------------------------------------------------------- *)
(* Free variables and freshness                                     *)
(* ---------------------------------------------------------------- *)

Fixpoint ty_fvars (T : ty) : list atom :=
  match T with
  | Ty_BVar _ => []
  | Ty_FVar X => [X]
  | Ty_Arrow T1 T2 => ty_fvars T1 ++ ty_fvars T2
  | Ty_All T1 => ty_fvars T1
  | Ty_Nat => []
  end.

Fixpoint tm_fvars (t : tm) : list atom :=
  match t with
  | tm_bvar _ => []
  | tm_fvar x => [x]
  | tm_abs T b => ty_fvars T ++ tm_fvars b
  | tm_app a b => tm_fvars a ++ tm_fvars b
  | tm_tabs b => tm_fvars b
  | tm_tapp a T => tm_fvars a ++ ty_fvars T
  | tm_zero => []
  | tm_succ a => tm_fvars a
  | tm_natrec n b s => tm_fvars n ++ tm_fvars b ++ tm_fvars s
  end.

Definition fresh_atom (l : list atom) : atom := S (fold_right Nat.max 0 l).

Lemma in_fold_max : forall l x, In x l -> x <= fold_right Nat.max 0 l.
Proof.
  induction l as [|a l IH]; intros x Hin.
  - inversion Hin.
  - simpl. destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + apply Nat.le_trans with (fold_right Nat.max 0 l).
      * apply IH; assumption.
      * apply Nat.le_max_r.
Qed.

Lemma fresh_atom_notin : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l Hin. unfold fresh_atom in Hin.
  pose proof (in_fold_max l (S (fold_right Nat.max 0 l)) Hin). lia.
Qed.

(* ---------------------------------------------------------------- *)
(* Erasure of type information from terms                           *)
(* ---------------------------------------------------------------- *)

Fixpoint erase (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => tm_fvar x
  | tm_abs _ b => tm_abs Ty_Nat (erase b)
  | tm_app a b => tm_app (erase a) (erase b)
  | tm_tabs b => tm_tabs (erase b)
  | tm_tapp a _ => tm_tapp (erase a) Ty_Nat
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (erase a)
  | tm_natrec n b s => tm_natrec (erase n) (erase b) (erase s)
  end.

Definition E (t : tm) : Prop := erase t = t.

Lemma erase_idem : forall t, erase (erase t) = erase t.
Proof. induction t; simpl; f_equal; auto. Qed.

Lemma erase_E : forall t, E (erase t).
Proof. intros t. unfold E. apply erase_idem. Qed.

Lemma E_fvar : forall x, E (tm_fvar x).
Proof. intros x. reflexivity. Qed.

Lemma E_zero : E tm_zero.
Proof. reflexivity. Qed.

Lemma E_abs : forall b, E b -> E (tm_abs Ty_Nat b).
Proof. intros b H. unfold E in *. simpl. rewrite H. reflexivity. Qed.

Lemma E_tabs : forall b, E b -> E (tm_tabs b).
Proof. intros b H. unfold E in *. simpl. rewrite H. reflexivity. Qed.

Lemma E_app : forall a b, E a -> E b -> E (tm_app a b).
Proof. intros a b Ha Hb. unfold E in *. simpl. rewrite Ha, Hb. reflexivity. Qed.

Lemma E_succ : forall a, E a -> E (tm_succ a).
Proof. intros a Ha. unfold E in *. simpl. rewrite Ha. reflexivity. Qed.

Lemma E_natrec : forall n b s, E n -> E b -> E s -> E (tm_natrec n b s).
Proof. intros n b s Hn Hb Hs. unfold E in *. simpl. rewrite Hn, Hb, Hs. reflexivity. Qed.

Lemma E_tapp : forall a, E a -> E (tm_tapp a Ty_Nat).
Proof. intros a Ha. unfold E in *. simpl. rewrite Ha. reflexivity. Qed.

(* ---------------------------------------------------------------- *)
(* Numeric values and values                                        *)
(* ---------------------------------------------------------------- *)

Lemma numeric_value_value : forall n, numeric_value n -> value n.
Proof. intros n H. apply v_nat. exact H. Qed.

Lemma numeric_value_no_step : forall n, numeric_value n -> forall u, ~ (n --> u).
Proof.
  intros n H. induction H as [|n H IH]; intros u Hstep.
  - inversion Hstep.
  - inversion Hstep; subst; try discriminate.
    eapply IH; eassumption.
Qed.

Lemma SN_step : forall t u, strongly_normalizing t -> t --> u -> strongly_normalizing u.
Proof.
  intros t u H Hs. destruct H as [t Hred]. apply Hred. assumption.
Qed.

Lemma SN_succ : forall n, strongly_normalizing n -> strongly_normalizing (tm_succ n).
Proof.
  intros n H. induction H as [n Hred IH].
  apply SN_intro. intros u Hs. inversion Hs; subst.
  apply IH. assumption.
Qed.

Lemma numeric_value_sn : forall n, numeric_value n -> strongly_normalizing n.
Proof.
  intros n H. induction H.
  - apply SN_intro. intros u Hstep. inversion Hstep.
  - apply SN_intro. intros u Hstep.
    inversion Hstep; subst.
    apply SN_succ. eapply SN_step; eassumption.
Qed.

Lemma numeric_value_lc : forall n, numeric_value n -> lc_tm_at 0 0 n.
Proof.
  intros n H. induction H.
  - constructor.
  - constructor. assumption.
Qed.

Lemma numeric_value_erase : forall n, numeric_value n -> erase n = n.
Proof.
  intros n H. induction H.
  - reflexivity.
  - simpl. f_equal. assumption.
Qed.

Lemma value_no_step : forall t, value t -> forall u, ~ (t --> u).
Proof.
  intros t H. induction H as [T t Hlc | t Hlc | n Hnv].
  - intros u Hstep. inversion Hstep.
  - intros u Hstep. inversion Hstep.
  - intros u Hstep. exact (numeric_value_no_step n Hnv u Hstep).
Qed.

Lemma value_no_step' : forall t u, value t -> t --> u -> False.
Proof. intros t u Hv Hs. eapply value_no_step; eassumption. Qed.

Lemma value_sn : forall t, value t -> strongly_normalizing t.
Proof.
  intros t H. induction H.
  - apply SN_intro. intros u Hstep. inversion Hstep.
  - apply SN_intro. intros u Hstep. inversion Hstep.
  - apply numeric_value_sn. assumption.
Qed.

(* ---------------------------------------------------------------- *)
(* Monotonicity of locally-closed predicates                        *)
(* ---------------------------------------------------------------- *)

Lemma lc_ty_at_mono : forall k T, lc_ty_at k T -> forall k', k <= k' -> lc_ty_at k' T.
Proof.
  intros k T H. induction H; intros k' Hle.
  - constructor. lia.
  - constructor.
  - constructor; [apply IHlc_ty_at1 | apply IHlc_ty_at2]; lia.
  - constructor. apply IHlc_ty_at. lia.
  - constructor.
Qed.

Lemma lc_tm_at_mono_K : forall K k t, lc_tm_at K k t -> forall K', K <= K' -> lc_tm_at K' k t.
Proof.
  intros K k t H. induction H; intros K' Hle.
  - constructor. assumption.
  - constructor.
  - constructor.
    + apply lc_ty_at_mono with (k := K); assumption.
    + apply IHlc_tm_at. assumption.
  - constructor; auto.
  - constructor. apply IHlc_tm_at. lia.
  - constructor.
    + apply IHlc_tm_at. assumption.
    + apply lc_ty_at_mono with (k := K); assumption.
  - constructor.
  - constructor. apply IHlc_tm_at. assumption.
  - constructor; auto.
Qed.

Lemma lc_tm_at_mono_k : forall K k t, lc_tm_at K k t -> forall k', k <= k' -> lc_tm_at K k' t.
Proof.
  intros K k t H. induction H; intros k' Hle.
  - constructor. lia.
  - constructor.
  - constructor.
    + assumption.
    + apply IHlc_tm_at. lia.
  - constructor; auto.
  - constructor. apply IHlc_tm_at. assumption.
  - constructor; auto.
  - constructor.
  - constructor. apply IHlc_tm_at. assumption.
  - constructor; auto.
Qed.

Lemma lc_tm_at_weaken : forall K K' k k' t, lc_tm_at K k t -> K <= K' -> k <= k' -> lc_tm_at K' k' t.
Proof.
  intros. apply lc_tm_at_mono_k with (k := k); [|assumption].
  apply lc_tm_at_mono_K with (K := K); assumption.
Qed.


(* ---------------------------------------------------------------- *)
(* Term substitution environments                                   *)
(* ---------------------------------------------------------------- *)

Fixpoint tm_subst_env (sigma : atom -> tm) (t : tm) : tm :=
  match t with
  | tm_bvar i => tm_bvar i
  | tm_fvar x => sigma x
  | tm_abs T b => tm_abs T (tm_subst_env sigma b)
  | tm_app a b => tm_app (tm_subst_env sigma a) (tm_subst_env sigma b)
  | tm_tabs b => tm_tabs (tm_subst_env sigma b)
  | tm_tapp a T => tm_tapp (tm_subst_env sigma a) T
  | tm_zero => tm_zero
  | tm_succ a => tm_succ (tm_subst_env sigma a)
  | tm_natrec n b sc => tm_natrec (tm_subst_env sigma n) (tm_subst_env sigma b) (tm_subst_env sigma sc)
  end.

Lemma tm_subst_env_id : forall t, tm_subst_env (fun x => tm_fvar x) t = t.
Proof. induction t; simpl; f_equal; auto. Qed.

(* ---------------------------------------------------------------- *)
(* Erasure commutation lemmas                                       *)
(* ---------------------------------------------------------------- *)

Lemma erase_open_tm_ty_rec : forall t k U, erase (open_tm_ty_rec k U t) = erase t.
Proof.
  induction t; intros k U; simpl; auto.
  - (* abs *) f_equal. apply IHt.
  - (* app *) f_equal; [apply IHt1 | apply IHt2].
  - (* tabs *) f_equal. apply IHt.
  - (* tapp *) f_equal. apply IHt.
  - (* succ *) f_equal. apply IHt.
  - (* natrec *) f_equal; [apply IHt1 | apply IHt2 | apply IHt3].
Qed.

Lemma erase_open_tm_rec : forall t k v, erase (open_tm_rec k v t) = open_tm_rec k (erase v) (erase t).
Proof.
  induction t; intros k v; simpl; auto.
  - (* bvar *) destruct (Nat.eqb k n); reflexivity.
  - (* abs *) f_equal. apply IHt.
  - (* app *) f_equal; [apply IHt1 | apply IHt2].
  - (* tabs *) f_equal. apply IHt.
  - (* tapp *) f_equal. apply IHt.
  - (* succ *) f_equal. apply IHt.
  - (* natrec *) f_equal; [apply IHt1 | apply IHt2 | apply IHt3].
Qed.

Lemma erase_subst_env : forall sigma t,
  (forall x, E (sigma x)) ->
  erase (tm_subst_env sigma t) = tm_subst_env sigma (erase t).
Proof.
  intros sigma t. induction t; intros HE; simpl; auto.
  - (* fvar *) apply HE.
  - (* abs *) f_equal. apply IHt. assumption.
  - (* app *) f_equal; [apply IHt1 | apply IHt2]; assumption.
  - (* tabs *) f_equal. apply IHt. assumption.
  - (* tapp *) f_equal. apply IHt. assumption.
  - (* succ *) f_equal. apply IHt. assumption.
  - (* natrec *) f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
Qed.

(* ---------------------------------------------------------------- *)
(* Locally closed terms have no free de Bruijn indices              *)
(* ---------------------------------------------------------------- *)

Lemma lc_open_tm_rec_id : forall K k t, lc_tm_at K k t ->
  forall j v, k <= j -> open_tm_rec j v t = t.
Proof.
  intros K k t H. induction H; intros j v Hle; simpl; auto.
  - (* bvar *) destruct (Nat.eqb j i) eqn:Eqb.
    + apply Nat.eqb_eq in Eqb. lia.
    + reflexivity.
  - (* abs *) f_equal. apply IHlc_tm_at. lia.
  - (* app *) f_equal; auto.
  - (* tabs *) f_equal. apply IHlc_tm_at. assumption.
  - (* tapp *) f_equal. apply IHlc_tm_at. assumption.
  - (* succ *) f_equal. apply IHlc_tm_at. assumption.
  - (* natrec *) f_equal; auto.
Qed.

Lemma E_open_tm_ty_rec : forall t, E t -> forall k U, open_tm_ty_rec k U t = t.
Proof.
  induction t; intros HE k U; simpl in *; try reflexivity.
  - (* abs *) unfold E in HE. simpl in HE. injection HE as HT Hb.
    subst. simpl. f_equal. apply IHt; assumption.
  - (* app *) unfold E in HE. simpl in HE. injection HE as Ha Hb.
    simpl. f_equal; [apply IHt1 | apply IHt2]; assumption.
  - (* tabs *) unfold E in HE. simpl in HE. injection HE as Hb.
    simpl. f_equal. apply IHt; assumption.
  - (* tapp *) unfold E in HE. simpl in HE. injection HE as Ha HT.
    subst. simpl. f_equal. apply IHt; assumption.
  - (* succ *) unfold E in HE. simpl in HE. injection HE as Ha.
    simpl. f_equal. apply IHt; assumption.
  - (* natrec *) unfold E in HE. simpl in HE. injection HE as Hn Hb Hs.
    simpl. f_equal; [apply IHt1 | apply IHt2 | apply IHt3]; assumption.
Qed.

Lemma E_open_tm_ty : forall t, E t -> forall U, open_tm_ty t U = t.
Proof. intros t H U. apply E_open_tm_ty_rec. assumption. Qed.

(* ---------------------------------------------------------------- *)
(* Substitution preserves locally-closedness                        *)
(* ---------------------------------------------------------------- *)

Lemma lc_ty_open_any : forall T K, lc_ty_at K T -> forall j U, lc_ty_at 0 U -> lc_ty_at K (open_ty_rec j U T).
Proof.
  induction T; intros K Hlc j U HU; simpl.
  - (* BVar *) destruct (Nat.eqb j n) eqn:Eqb.
    + apply Nat.eqb_eq in Eqb; subst. apply lc_ty_at_mono with (k := 0); [assumption|lia].
    + inversion Hlc; subst. constructor. assumption.
  - (* FVar *) constructor.
  - (* Arrow *) inversion Hlc; subst. constructor.
    + apply IHT1; assumption.
    + apply IHT2; assumption.
  - (* All *) inversion Hlc; subst. constructor.
    apply IHT with (K := S K) (j := S j) (U := U); assumption.
  - (* Nat *) constructor.
Qed.

Lemma lc_ty_open_drop : forall T j, lc_ty_at (S j) T -> forall U, lc_ty_at 0 U -> lc_ty_at j (open_ty_rec j U T).
Proof.
  induction T; intros j Hlc U HU; simpl.
  - (* BVar *) destruct (Nat.eqb j n) eqn:Eqb.
    + apply Nat.eqb_eq in Eqb; subst. apply lc_ty_at_mono with (k := 0); [assumption|lia].
    + apply Nat.eqb_neq in Eqb. inversion Hlc; subst. apply lc_ty_bvar. lia.
  - (* FVar *) constructor.
  - (* Arrow *) inversion Hlc; subst. constructor.
    + apply IHT1; assumption.
    + apply IHT2; assumption.
  - (* All *) inversion Hlc; subst. constructor.
    apply IHT with (j := S j) (U := U); assumption.
  - (* Nat *) constructor.
Qed.

Lemma lc_ty_open_inv_j : forall T j U, lc_ty_at j (open_ty_rec j U T) -> lc_ty_at (S j) T.
Proof.
  induction T; intros j U Hlc; simpl in Hlc.
  - (* BVar *) destruct (Nat.eqb j n) eqn:Eqb.
    + apply Nat.eqb_eq in Eqb; subst. apply lc_ty_bvar. lia.
    + apply Nat.eqb_neq in Eqb. inversion Hlc; subst. apply lc_ty_bvar. lia.
  - (* FVar *) constructor.
  - (* Arrow *) inversion Hlc; subst. constructor.
    + eapply IHT1; eassumption.
    + eapply IHT2; eassumption.
  - (* All *) inversion Hlc; subst. constructor.
    eapply IHT; eassumption.
  - (* Nat *) constructor.
Qed.

Lemma lc_open_tm_ty_drop : forall t j k, lc_tm_at (S j) k t ->
  forall U, lc_ty_at 0 U -> lc_tm_at j k (open_tm_ty_rec j U t).
Proof.
  induction t; intros j k Hlc U HU; simpl.
  - (* BVar *) inversion Hlc; subst. apply lc_tm_bvar. assumption.
  - (* FVar *) constructor.
  - (* Abs *) inversion Hlc; subst. constructor.
    + apply lc_ty_open_drop; assumption.
    + apply IHt; assumption.
  - (* App *) inversion Hlc; subst. constructor.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - (* TAbs *) inversion Hlc; subst. constructor.
    apply IHt with (j := S j) (U := U); assumption.
  - (* TApp *) inversion Hlc; subst. constructor.
    + apply IHt; assumption.
    + apply lc_ty_open_drop; assumption.
  - (* Zero *) constructor.
  - (* Succ *) inversion Hlc; subst. constructor. apply IHt; assumption.
  - (* Rec *) inversion Hlc; subst. constructor.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
    + apply IHt3; assumption.
Qed.

Lemma lc_open_tm_ty_inv : forall t j k U, lc_tm_at j k (open_tm_ty_rec j U t) ->
  lc_tm_at (S j) k t.
Proof.
  induction t; intros j k U Hlc; simpl in Hlc.
  - (* BVar *) inversion Hlc; subst. apply lc_tm_bvar. assumption.
  - (* FVar *) constructor.
  - (* Abs *) inversion Hlc; subst. constructor.
    + eapply lc_ty_open_inv_j; eassumption.
    + eapply IHt; eassumption.
  - (* App *) inversion Hlc; subst. constructor.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
  - (* TAbs *) inversion Hlc; subst. constructor.
    eapply IHt; eassumption.
  - (* TApp *) inversion Hlc; subst. constructor.
    + eapply IHt; eassumption.
    + eapply lc_ty_open_inv_j; eassumption.
  - (* Zero *) constructor.
  - (* Succ *) inversion Hlc; subst. constructor. eapply IHt; eassumption.
  - (* Rec *) inversion Hlc; subst. constructor.
    + eapply IHt1; eassumption.
    + eapply IHt2; eassumption.
    + eapply IHt3; eassumption.
Qed.

Lemma lc_open_tm_rec : forall t K k, lc_tm_at K (S k) t ->
  forall v, lc_tm_at K k v -> lc_tm_at K k (open_tm_rec k v t).
Proof.
  induction t; intros K k Hlc v Hv; simpl.
  - (* BVar *) inversion Hlc; subst. destruct (Nat.eqb k n) eqn:Eqb.
    + apply Nat.eqb_eq in Eqb; subst. assumption.
    + apply Nat.eqb_neq in Eqb. constructor. lia.
  - (* FVar *) constructor.
  - (* Abs *) inversion Hlc; subst. constructor.
    + assumption.
    + apply IHt with (k := S k); [assumption|].
      apply lc_tm_at_mono_k with (k := k); [assumption|lia].
  - (* App *) inversion Hlc; subst. constructor.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - (* TAbs *) inversion Hlc; subst. constructor.
    apply IHt with (K := S K) (k := k); [assumption|].
    apply lc_tm_at_mono_K with (K := K); [assumption|lia].
  - (* TApp *) inversion Hlc; subst. constructor.
    + apply IHt; assumption.
    + assumption.
  - (* Zero *) constructor.
  - (* Succ *) inversion Hlc; subst. constructor. apply IHt; assumption.
  - (* Rec *) inversion Hlc; subst. constructor.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
    + apply IHt3; assumption.
Qed.

Lemma lc_subst_env : forall t K k, lc_tm_at K k t ->
  forall sigma, (forall x, lc_tm_at 0 0 (sigma x)) -> lc_tm_at K k (tm_subst_env sigma t).
Proof.
  induction t; intros K k Hlc sigma Hsig; simpl.
  - (* BVar *) inversion Hlc; subst. constructor. assumption.
  - (* FVar *) apply lc_tm_at_weaken with (K := 0) (k := 0); [apply Hsig|lia|lia].
  - (* Abs *) inversion Hlc; subst. constructor.
    + assumption.
    + apply IHt with (k := S k); assumption.
  - (* App *) inversion Hlc; subst. constructor.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
  - (* TAbs *) inversion Hlc; subst. constructor.
    apply IHt with (K := S K) (k := k); assumption.
  - (* TApp *) inversion Hlc; subst. constructor.
    + apply IHt; assumption.
    + assumption.
  - (* Zero *) constructor.
  - (* Succ *) inversion Hlc; subst. constructor. apply IHt; assumption.
  - (* Rec *) inversion Hlc; subst. constructor.
    + apply IHt1; assumption.
    + apply IHt2; assumption.
    + apply IHt3; assumption.
Qed.

Lemma tm_subst_env_open : forall sigma, (forall x, lc_tm_at 0 0 (sigma x)) ->
  forall t k v,
    tm_subst_env sigma (open_tm_rec k v t) =
    open_tm_rec k (tm_subst_env sigma v) (tm_subst_env sigma t).
Proof.
  intros sigma Hsig t. induction t; intros k v; simpl.
  - (* BVar *) destruct (Nat.eqb k n); reflexivity.
  - (* FVar *) symmetry. apply lc_open_tm_rec_id with (K := 0) (k := 0); [apply Hsig|lia].
  - (* Abs *) f_equal. apply IHt.
  - (* App *) f_equal; [apply IHt1|apply IHt2].
  - (* TAbs *) f_equal. apply IHt.
  - (* TApp *) f_equal. apply IHt.
  - (* Zero *) reflexivity.
  - (* Succ *) f_equal. apply IHt.
  - (* Rec *) f_equal; [apply IHt1|apply IHt2|apply IHt3].
Qed.

Lemma lc_ty_open_inv : forall T k j U, j <= k -> lc_ty_at k (open_ty_rec j U T) -> lc_ty_at (S k) T.
Proof.
  induction T; intros k j U Hle Hlc; simpl in Hlc.
  - (* BVar *) destruct (Nat.eqb j n) eqn:Eqb.
    + apply Nat.eqb_eq in Eqb; subst. apply lc_ty_bvar. lia.
    + inversion Hlc; subst. apply lc_ty_bvar. lia.
  - (* FVar *) constructor.
  - (* Arrow *) inversion Hlc; subst. constructor.
    + eapply IHT1; eassumption.
    + eapply IHT2; eassumption.
  - (* All *) inversion Hlc; subst. constructor.
    apply IHT with (k := S k) (j := S j) (U := U); [lia|assumption].
  - (* Nat *) constructor.
Qed.

Lemma lc_tm_ty_open_inv : forall t K k j U, j <= K ->
  lc_tm_at K k (open_tm_ty_rec j U t) -> lc_tm_at (S K) k t.
Proof.
  induction t; intros K k j U Hle Hlc; simpl in Hlc.
  - (* BVar *) inversion Hlc; subst. apply lc_tm_bvar. lia.
  - (* FVar *) apply lc_tm_fvar.
  - (* Abs *) inversion Hlc; subst. constructor.
    + eapply lc_ty_open_inv; eassumption.
    + apply IHt with (j := j) (U := U); assumption.
  - (* App *) inversion Hlc; subst. constructor.
    + apply IHt1 with (j := j) (U := U); assumption.
    + apply IHt2 with (j := j) (U := U); assumption.
  - (* TAbs *) inversion Hlc; subst. constructor.
    apply IHt with (K := S K) (j := S j) (U := U); [lia|assumption].
  - (* TApp *) inversion Hlc; subst. constructor.
    + apply IHt with (j := j) (U := U); assumption.
    + eapply lc_ty_open_inv; eassumption.
  - (* Zero *) constructor.
  - (* Succ *) inversion Hlc; subst. constructor. apply IHt with (j := j) (U := U); assumption.
  - (* Rec *) inversion Hlc; subst. constructor.
    + apply IHt1 with (j := j) (U := U); assumption.
    + apply IHt2 with (j := j) (U := U); assumption.
    + apply IHt3 with (j := j) (U := U); assumption.
Qed.

Lemma lc_tm_open_inv : forall t K k j u, j <= k ->
  lc_tm_at K k (open_tm_rec j u t) -> lc_tm_at K k u -> lc_tm_at K (S k) t.
Proof.
  induction t; intros K k j u Hle Hlc Hu; simpl in Hlc.
  - (* BVar *) destruct (Nat.eqb j n) eqn:Eqb.
    + apply Nat.eqb_eq in Eqb; subst. apply lc_tm_bvar. lia.
    + inversion Hlc; subst. apply lc_tm_bvar. lia.
  - (* FVar *) constructor.
  - (* Abs *) inversion Hlc; subst. constructor.
    + assumption.
    + apply IHt with (j := S j) (u := u); [lia|assumption|].
      apply lc_tm_at_mono_k with (k := k); [assumption|lia].
  - (* App *) inversion Hlc; subst. constructor.
    + apply IHt1 with (j := j) (u := u); assumption.
    + apply IHt2 with (j := j) (u := u); assumption.
  - (* TAbs *) inversion Hlc; subst. constructor.
    apply IHt with (K := S K) (k := k) (j := j) (u := u); [assumption|assumption|].
    apply lc_tm_at_mono_K with (K := K); [assumption|lia].
  - (* TApp *) inversion Hlc; subst. constructor.
    + apply IHt with (j := j) (u := u); assumption.
    + assumption.
  - (* Zero *) constructor.
  - (* Succ *) inversion Hlc; subst. constructor. apply IHt with (j := j) (u := u); assumption.
  - (* Rec *) inversion Hlc; subst. constructor.
    + apply IHt1 with (j := j) (u := u); assumption.
    + apply IHt2 with (j := j) (u := u); assumption.
    + apply IHt3 with (j := j) (u := u); assumption.
Qed.

Lemma value_lc : forall t, value t -> lc_tm_at 0 0 t.
Proof.
  intros t H. induction H.
  - assumption.
  - assumption.
  - apply numeric_value_lc. assumption.
Qed.

Lemma erase_lc : forall t K k, lc_tm_at K k t -> lc_tm_at K k (erase t).
Proof.
  induction t; intros K k Hlc; simpl.
  - (* BVar *) assumption.
  - (* FVar *) constructor.
  - (* Abs *) inversion Hlc; subst. constructor.
    + constructor.
    + apply IHt. assumption.
  - (* App *) inversion Hlc; subst. constructor.
    + apply IHt1. assumption.
    + apply IHt2. assumption.
  - (* TAbs *) inversion Hlc; subst. constructor.
    apply IHt with (K := S K). assumption.
  - (* TApp *) inversion Hlc; subst. constructor.
    + apply IHt. assumption.
    + constructor.
  - (* Zero *) constructor.
  - (* Succ *) inversion Hlc; subst. constructor. apply IHt. assumption.
  - (* Rec *) inversion Hlc; subst. constructor.
    + apply IHt1. assumption.
    + apply IHt2. assumption.
    + apply IHt3. assumption.
Qed.

Lemma value_erase : forall t, value t -> value (erase t).
Proof.
  intros t H. induction H as [T t Hlc | t Hlc | n Hnv].
  - simpl. apply v_abs. apply (erase_lc (tm_abs T t) 0 0 Hlc).
  - simpl. apply v_tabs. apply (erase_lc (tm_tabs t) 0 0 Hlc).
  - simpl. rewrite numeric_value_erase by assumption. apply v_nat. assumption.
Qed.

Lemma lc_bvar_inv : forall K k i, lc_tm_at K k (tm_bvar i) -> i < k.
Proof. intros K k i H. inversion H. assumption. Qed.

Lemma lc_abs_inv : forall K k T t, lc_tm_at K k (tm_abs T t) -> lc_ty_at K T /\ lc_tm_at K (S k) t.
Proof. intros K k T t H. inversion H; subst; split; assumption. Qed.

Lemma lc_app_inv : forall K k a b, lc_tm_at K k (tm_app a b) -> lc_tm_at K k a /\ lc_tm_at K k b.
Proof. intros K k a b H. inversion H; subst; split; assumption. Qed.

Lemma lc_tabs_inv : forall K k t, lc_tm_at K k (tm_tabs t) -> lc_tm_at (S K) k t.
Proof. intros K k t H. inversion H; subst; assumption. Qed.

Lemma lc_tapp_inv : forall K k a T, lc_tm_at K k (tm_tapp a T) -> lc_tm_at K k a /\ lc_ty_at K T.
Proof. intros K k a T H. inversion H; subst; split; assumption. Qed.

Lemma lc_succ_inv : forall K k a, lc_tm_at K k (tm_succ a) -> lc_tm_at K k a.
Proof. intros K k a H. inversion H; subst; assumption. Qed.

Lemma lc_rec_inv : forall K k n b s, lc_tm_at K k (tm_natrec n b s) -> lc_tm_at K k n /\ lc_tm_at K k b /\ lc_tm_at K k s.
Proof. intros K k n b s H. inversion H; subst; repeat split; assumption. Qed.

Lemma lc_step : forall t u, lc_tm_at 0 0 t -> t --> u -> lc_tm_at 0 0 u.
Proof.
  intros t u Hlc Hstep. revert Hlc. induction Hstep; intros Hlc.
  - (* AppAbs *) apply lc_app_inv in Hlc. destruct Hlc as [Habs Hv].
    apply lc_abs_inv in Habs. destruct Habs as [Hty Hbody].
    simpl. apply lc_open_tm_rec with (k := 0); [assumption|].
    apply value_lc. assumption.
  - (* App1 *) apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    simpl. constructor; [apply IHHstep; assumption | assumption].
  - (* App2 *) apply lc_app_inv in Hlc. destruct Hlc as [H1 H2].
    simpl. constructor; [assumption | apply IHHstep; assumption].
  - (* TAppTabs *) apply lc_tapp_inv in Hlc. destruct Hlc as [Htabs HT].
    apply lc_tabs_inv in Htabs.
    simpl. apply lc_open_tm_ty_drop with (j := 0); [|exact HT].
    exact Htabs.
  - (* TApp *) apply lc_tapp_inv in Hlc. destruct Hlc as [H1 H2].
    simpl. constructor; [apply IHHstep; assumption | assumption].
  - (* Succ *) apply lc_succ_inv in Hlc.
    simpl. constructor. apply IHHstep; assumption.
  - (* RecArg *) apply lc_rec_inv in Hlc. destruct Hlc as [Hn [Hb Hs]].
    simpl. constructor; [apply IHHstep; assumption | assumption | assumption].
  - (* RecBase *) apply lc_rec_inv in Hlc. destruct Hlc as [Hn [Hb Hs]].
    simpl. constructor; [assumption | apply IHHstep; assumption | assumption].
  - (* RecStep *) apply lc_rec_inv in Hlc. destruct Hlc as [Hn [Hb Hs]].
    simpl. constructor; [assumption | assumption | apply IHHstep; assumption].
  - (* RecZero *) apply lc_rec_inv in Hlc. destruct Hlc as [Hn [Hb Hs]].
    simpl. assumption.
  - (* RecSucc *) apply lc_rec_inv in Hlc. destruct Hlc as [Hn [Hb Hs]].
    simpl. constructor.
    + constructor.
      * apply value_lc. assumption.
      * apply numeric_value_lc. assumption.
    + constructor.
      * apply numeric_value_lc. assumption.
      * assumption.
      * assumption.
Qed.

Lemma E_app_inv : forall a b, E (tm_app a b) -> E a /\ E b.
Proof. intros a b H. unfold E in *. simpl in H. injection H as H1 H2. split; assumption. Qed.

Lemma E_abs_inv : forall T b, E (tm_abs T b) -> T = Ty_Nat /\ E b.
Proof. intros T b H. unfold E in *. simpl in H. injection H as H1 H2. subst. split; [reflexivity|assumption]. Qed.

Lemma E_tabs_inv : forall b, E (tm_tabs b) -> E b.
Proof. intros b H. unfold E in *. simpl in H. injection H as H1. assumption. Qed.

Lemma E_tapp_inv : forall a T, E (tm_tapp a T) -> E a /\ T = Ty_Nat.
Proof. intros a T H. unfold E in *. simpl in H. injection H as H1 H2. subst. split; [assumption|reflexivity]. Qed.

Lemma E_succ_inv : forall a, E (tm_succ a) -> E a.
Proof. intros a H. unfold E in *. simpl in H. injection H as H1. assumption. Qed.

Lemma E_natrec_inv : forall n b s, E (tm_natrec n b s) -> E n /\ E b /\ E s.
Proof. intros n b s H. unfold E in *. simpl in H. injection H as H1 H2 H3. repeat split; assumption. Qed.

Lemma E_step : forall t u, E t -> t --> u -> E u.
Proof.
  intros t u HE Hstep. revert HE. induction Hstep; intros HE.
  - (* AppAbs *) apply E_app_inv in HE. destruct HE as [Habs Hv].
    apply E_abs_inv in Habs. destruct Habs as [HT Hb].
    unfold E. unfold open_tm. rewrite erase_open_tm_rec, Hb, Hv. reflexivity.
  - (* App1 *) apply E_app_inv in HE. destruct HE as [H1 H2].
    apply E_app; [apply IHHstep; assumption|assumption].
  - (* App2 *) apply E_app_inv in HE. destruct HE as [H1 H2].
    apply E_app; [assumption|apply IHHstep; assumption].
  - (* TAppTabs *) apply E_tapp_inv in HE. destruct HE as [Htabs HT].
    apply E_tabs_inv in Htabs. rewrite HT.
    unfold E. unfold open_tm_ty.
    rewrite erase_open_tm_ty_rec, Htabs, (E_open_tm_ty_rec t Htabs 0 Ty_Nat). reflexivity.
  - (* TApp *) apply E_tapp_inv in HE. destruct HE as [H1 HT]. rewrite HT.
    apply E_tapp. apply IHHstep. assumption.
  - (* Succ *) apply E_succ_inv in HE.
    apply E_succ. apply IHHstep. assumption.
  - (* RecArg *) apply E_natrec_inv in HE. destruct HE as [Hn [Hb Hs]].
    apply E_natrec; [apply IHHstep; assumption|assumption|assumption].
  - (* RecBase *) apply E_natrec_inv in HE. destruct HE as [Hn [Hb Hs]].
    apply E_natrec; [assumption|apply IHHstep; assumption|assumption].
  - (* RecStep *) apply E_natrec_inv in HE. destruct HE as [Hn [Hb Hs]].
    apply E_natrec; [assumption|assumption|apply IHHstep; assumption].
  - (* RecZero *) apply E_natrec_inv in HE. destruct HE as [Hn [Hb Hs]].
    assumption.
  - (* RecSucc *) apply E_natrec_inv in HE. destruct HE as [Hn' [Hb Hs]].
    apply E_succ_inv in Hn'.
    apply E_app.
    + apply E_app; assumption.
    + apply E_natrec; assumption.
Qed.

Lemma step_erase : forall t u, t --> u -> erase t --> erase u.
Proof.
  intros t u Hstep. induction Hstep.
  - (* AppAbs *) unfold open_tm. rewrite erase_open_tm_rec. simpl.
    eapply ST_AppAbs.
    + apply (erase_lc (tm_abs T t) 0 0 H).
    + apply value_erase. assumption.
  - (* App1 *) simpl. eapply ST_App1.
    + eassumption.
    + apply erase_lc. assumption.
  - (* App2 *) simpl. eapply ST_App2.
    + apply value_erase. assumption.
    + eassumption.
  - (* TAppTabs *) unfold open_tm_ty. rewrite erase_open_tm_ty_rec. simpl.
    rewrite <- (E_open_tm_ty_rec (erase t) (erase_E t) 0 Ty_Nat) at 2.
    eapply ST_TAppTabs.
    + apply (erase_lc (tm_tabs t) 0 0 H).
    + constructor.
  - (* TApp *) simpl. eapply ST_TApp.
    + eassumption.
    + constructor.
  - (* Succ *) simpl. apply ST_Succ. assumption.
  - (* RecArg *) simpl. eapply ST_RecArg.
    + eassumption.
    + apply erase_lc. assumption.
    + apply erase_lc. assumption.
  - (* RecBase *) simpl. eapply ST_RecBase.
    + rewrite numeric_value_erase by assumption. assumption.
    + eassumption.
    + apply erase_lc. assumption.
  - (* RecStep *) simpl. eapply ST_RecStep.
    + rewrite numeric_value_erase by assumption. assumption.
    + apply value_erase. assumption.
    + eassumption.
  - (* RecZero *) simpl. eapply ST_RecZero.
    + apply value_erase. assumption.
    + apply value_erase. assumption.
  - (* RecSucc *) simpl. eapply ST_RecSucc.
    + rewrite numeric_value_erase by assumption. assumption.
    + apply value_erase. assumption.
    + apply value_erase. assumption.
Qed.

Lemma SN_erase : forall t, strongly_normalizing (erase t) -> strongly_normalizing t.
Proof.
  intros t H. remember (erase t) as e eqn:He. revert t He.
  induction H as [e Hred IH]; intros t He.
  apply SN_intro. intros u Hstep.
  apply (IH (erase u)).
  - rewrite He. apply step_erase. assumption.
  - reflexivity.
Qed.


(* ---------------------------------------------------------------- *)
(* Type-level properties of well-formedness                         *)
(* ---------------------------------------------------------------- *)

Definition incl_atoms (l1 l2 : list atom) : Prop := forall X, In X l1 -> In X l2.

Lemma incl_atoms_app_l : forall l1 l2 l3, incl_atoms l1 l2 -> incl_atoms l1 (l2 ++ l3).
Proof. intros l1 l2 l3 H X HX. apply in_app_iff. left. apply H. assumption. Qed.

Lemma ty_fvars_open_rec_incl : forall T j U, incl_atoms (ty_fvars T) (ty_fvars (open_ty_rec j U T)).
Proof.
  induction T; intros j U; simpl.
  - (* BVar *) destruct (Nat.eqb j n); simpl; intros Y H; inversion H.
  - (* FVar *) intros Y H. assumption.
  - (* Arrow *) intros Y H. apply in_app_iff in H. apply in_app_iff.
    destruct H as [H|H]; [left|right]; [apply IHT1|apply IHT2]; assumption.
  - (* All *) apply IHT.
  - (* Nat *) intros Y H. inversion H.
Qed.

Lemma lc_ty_open_id_gen : forall T k, lc_ty_at k T -> forall j U, k <= j -> open_ty_rec j U T = T.
Proof.
  induction T; intros k Hlc j U Hle; simpl.
  - (* BVar *) inversion Hlc; subst. destruct (Nat.eqb j n) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
  - (* FVar *) reflexivity.
  - (* Arrow *) inversion Hlc; subst. f_equal.
    + apply IHT1 with (k := k); assumption.
    + apply IHT2 with (k := k); assumption.
  - (* All *) inversion Hlc; subst. f_equal. apply IHT with (k := S k); [assumption|lia].
  - (* Nat *) reflexivity.
Qed.

Lemma lc_ty_open_id : forall T, lc_ty_at 0 T -> forall j U, open_ty_rec j U T = T.
Proof. intros T H j U. apply lc_ty_open_id_gen with (k := 0); [assumption|lia]. Qed.

Lemma ty_subst_open_rec : forall V X U Z j, lc_ty_at 0 U ->
  ty_subst X U (open_ty_rec j (Ty_FVar Z) V) =
  open_ty_rec j (ty_subst X U (Ty_FVar Z)) (ty_subst X U V).
Proof.
  induction V as [n | Y | V1 IH1 V2 IH2 | V1 IH1 | ]; intros X U Z j HU; simpl.
  - (* BVar *) destruct (Nat.eqb j n); reflexivity.
  - (* FVar *) destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E; subst.
      symmetry. apply lc_ty_open_id_gen with (k := 0); [assumption|lia].
    + simpl. reflexivity.
  - (* Arrow *) f_equal; [apply IH1|apply IH2]; assumption.
  - (* All *) f_equal. apply IH1 with (j := S j). assumption.
  - (* Nat *) reflexivity.
Qed.

Lemma not_in_app_l : forall (l1 l2 : list atom) (X : atom), ~ In X (l1 ++ l2) -> ~ In X l1.
Proof. intros l1 l2 X H Hc. apply H. apply in_app_iff. left. assumption. Qed.

Lemma not_in_app_r : forall (l1 l2 : list atom) (X : atom), ~ In X (l1 ++ l2) -> ~ In X l2.
Proof. intros l1 l2 X H Hc. apply H. apply in_app_iff. right. assumption. Qed.

Lemma not_in_single : forall (X Y : atom), ~ In X (Y :: nil) -> X <> Y.
Proof. intros X Y H Hc. apply H. subst. simpl. auto. Qed.

Lemma wf_ty_fvars : forall Delta T, wf_ty Delta T -> forall Y, In Y (ty_fvars T) -> In Y Delta.
Proof.
  intros Delta T Hw. induction Hw as [D X HX | D T1 T2 H1 IH1 H2 IH2 | L D T0 Hfun IHfun | D];
  intros Y Hy.
  - (* Var *) simpl in Hy. destruct Hy as [->|[]]. assumption.
  - (* Arrow *) simpl in Hy. apply in_app_iff in Hy. destruct Hy as [Hy|Hy].
    + apply IH1. assumption.
    + apply IH2. assumption.
  - (* All *) simpl in Hy.
    set (Z := fresh_atom ((L ++ D) ++ (Y :: nil))).
    assert (HZnot : ~ In Z ((L ++ D) ++ (Y :: nil))) by apply fresh_atom_notin.
    assert (HZLD : ~ In Z (L ++ D)) by (apply not_in_app_l with (l2 := (Y :: nil)); assumption).
    assert (HZY' : ~ In Z (Y :: nil)) by (apply not_in_app_r with (l1 := (L ++ D)); assumption).
    assert (HZL : ~ In Z L) by (apply not_in_app_l with (l2 := D); assumption).
    assert (HZD : ~ In Z D) by (apply not_in_app_r with (l1 := L); assumption).
    assert (HZY : Z <> Y) by (apply not_in_single; assumption).
    assert (Hin : In Y (ty_fvars (open_ty T0 (Ty_FVar Z)))).
    { apply ty_fvars_open_rec_incl. assumption. }
    pose proof (IHfun Z HZL Y Hin) as Hres.
    simpl in Hres. destruct Hres as [Hres|Hres].
    + exfalso. apply HZY. congruence.
    + assumption.
  - (* Nat *) simpl in Hy. inversion Hy.
Qed.

Lemma wf_ty_lc : forall Delta T, wf_ty Delta T -> locally_closed_ty T.
Proof.
  intros Delta T Hw. induction Hw as [D X HX | D T1 T2 H1 IH1 H2 IH2 | L D T0 Hfun IHfun | D].
  - (* Var *) constructor.
  - (* Arrow *) constructor; assumption.
  - (* All *) constructor.
    set (Z := fresh_atom L).
    apply lc_ty_open_inv_j with (j := 0) (U := Ty_FVar Z).
    apply IHfun. apply fresh_atom_notin.
  - (* Nat *) constructor.
Qed.

Lemma wf_ty_mono : forall Delta T, wf_ty Delta T -> forall Delta', incl_atoms Delta Delta' -> wf_ty Delta' T.
Proof.
  intros Delta T Hw. induction Hw as [D X HX | D T1 T2 H1 IH1 H2 IH2 | L D T0 Hfun IHfun | D];
  intros Delta' Hincl.
  - (* Var *) apply WF_Var. apply Hincl. assumption.
  - (* Arrow *) constructor; auto.
  - (* All *) apply WF_All with (L := L). intros Z HZ.
    apply IHfun; [assumption|].
    intros W HW. simpl in HW. destruct HW as [->|HW].
    + left. reflexivity.
    + right. apply Hincl. assumption.
  - (* Nat *) constructor.
Qed.

Lemma wf_ty_cons : forall Delta T, wf_ty Delta T -> forall X, wf_ty (X :: Delta) T.
Proof.
  intros Delta T H X. apply wf_ty_mono with (Delta := Delta); [assumption|].
  intros Y HY. simpl. right. assumption.
Qed.

Fixpoint ty_subst_env (sigma : atom -> ty) (T : ty) : ty :=
  match T with
  | Ty_BVar i => Ty_BVar i
  | Ty_FVar X => sigma X
  | Ty_Arrow T1 T2 => Ty_Arrow (ty_subst_env sigma T1) (ty_subst_env sigma T2)
  | Ty_All T1 => Ty_All (ty_subst_env sigma T1)
  | Ty_Nat => Ty_Nat
  end.

Lemma ty_subst_env_single : forall X U T,
  ty_subst X U T = ty_subst_env (fun Y => if Nat.eqb X Y then U else Ty_FVar Y) T.
Proof.
  induction T; simpl; try reflexivity; f_equal; assumption.
Qed.

Lemma ty_subst_env_ext : forall T sigma sigma',
  (forall X, In X (ty_fvars T) -> sigma X = sigma' X) ->
  ty_subst_env sigma T = ty_subst_env sigma' T.
Proof.
  induction T; intros sigma sigma' Hagree; simpl.
  - reflexivity.
  - apply Hagree. simpl. auto.
  - f_equal; [apply IHT1|apply IHT2]; intros X HX;
      apply Hagree; simpl; apply in_app_iff; [left|right]; assumption.
  - f_equal. apply IHT. intros X HX. apply Hagree. simpl. assumption.
  - reflexivity.
Qed.

Lemma ty_subst_env_lc : forall T k, lc_ty_at k T ->
  forall sigma, (forall X, lc_ty_at 0 (sigma X)) -> lc_ty_at k (ty_subst_env sigma T).
Proof.
  induction T; intros k Hlc sigma Hsig; simpl.
  - (* BVar *) inversion Hlc; subst. constructor. assumption.
  - (* FVar *) apply lc_ty_at_mono with (k := 0); [apply Hsig|lia].
  - (* Arrow *) inversion Hlc; subst. constructor.
    + apply IHT1; assumption.
    + apply IHT2; assumption.
  - (* All *) inversion Hlc; subst. constructor.
    apply IHT with (k := S k).
    + assumption.
    + intro X. apply lc_ty_at_mono with (k := 0); [apply Hsig|lia].
  - (* Nat *) constructor.
Qed.

Lemma lc_ty_open_sigma_id : forall T, lc_ty_at 0 T -> forall j W, open_ty_rec j W T = T.
Proof. intros T H j W. exact (lc_ty_open_id_gen T 0 H j W (Nat.le_0_l j)). Qed.

Lemma ty_subst_env_open_rec : forall T j Y sigma,
  (forall X, lc_ty_at 0 (sigma X)) ->
  ty_subst_env sigma (open_ty_rec j (Ty_FVar Y) T) =
  open_ty_rec j (sigma Y) (ty_subst_env sigma T).
Proof.
  induction T; intros j Y sigma Hsig; simpl.
  - (* BVar *) destruct (Nat.eqb j n); reflexivity.
  - (* FVar X *) symmetry. apply lc_ty_open_sigma_id. apply Hsig.
  - (* Arrow *) f_equal; [apply IHT1|apply IHT2]; assumption.
  - (* All *) f_equal. apply IHT. assumption.
  - (* Nat *) reflexivity.
Qed.

Lemma wf_ty_subst_env : forall D T, wf_ty D T ->
  forall sigma D', (forall X, In X D -> wf_ty D' (sigma X)) ->
  (forall X, lc_ty_at 0 (sigma X)) ->
  wf_ty D' (ty_subst_env sigma T).
Proof.
  intros D T Hw. induction Hw as [D0 Y HY | D0 T1 T2 H1 IH1 H2 IH2 | L D0 T0 Hfun IHfun | D0];
  intros sigma D' Hrange Hlc.
  - (* Var *) simpl. apply Hrange. assumption.
  - (* Arrow *) simpl. constructor; auto.
  - (* All *) simpl. apply WF_All with (L := (L ++ D') ++ ty_fvars T0).
    intros Y HY.
    assert (HYLD : ~ In Y (L ++ D')) by (apply not_in_app_l with (l2 := ty_fvars T0); assumption).
    assert (HYL : ~ In Y L) by (apply not_in_app_l with (l2 := D'); assumption).
    assert (HYD' : ~ In Y D') by (apply not_in_app_r with (l1 := L); assumption).
    assert (HYT0 : ~ In Y (ty_fvars T0)) by (apply not_in_app_r with (l1 := L ++ D'); assumption).
    pose proof (Hfun Y HYL) as Hbody.
    pose proof (IHfun Y HYL (fun Z => if Nat.eqb Y Z then Ty_FVar Y else sigma Z) (Y :: D')) as HIH.
    assert (Hrange' : forall Z, In Z (Y :: D0) -> wf_ty (Y :: D') ((fun Z0 => if Nat.eqb Y Z0 then Ty_FVar Y else sigma Z0) Z)).
    { intros Z HZ. simpl in HZ. destruct HZ as [HZY|HZD].
      - subst Z. destruct (Nat.eqb Y Y) eqn:E.
        + apply WF_Var. simpl. left. reflexivity.
        + apply Nat.eqb_neq in E. exfalso. apply E. reflexivity.
      - destruct (Nat.eqb Y Z) eqn:E.
        + apply Nat.eqb_eq in E. subst. apply WF_Var. simpl. left. reflexivity.
        + apply Nat.eqb_neq in E. apply wf_ty_cons. apply Hrange. assumption. }
    assert (Hlc' : forall Z, lc_ty_at 0 ((fun Z0 => if Nat.eqb Y Z0 then Ty_FVar Y else sigma Z0) Z)).
    { intro Z. destruct (Nat.eqb Y Z) eqn:E. + constructor. + apply Hlc. }
    specialize (HIH Hrange' Hlc').
    unfold open_ty in HIH.
    rewrite ty_subst_env_open_rec in HIH by assumption.
    simpl in HIH.
    rewrite Nat.eqb_refl in HIH. simpl in HIH.
    rewrite ty_subst_env_ext with (sigma := (fun Z => if Nat.eqb Y Z then Ty_FVar Y else sigma Z)) (sigma' := sigma) in HIH.
    2: { intros X HX. destruct (Nat.eqb Y X) eqn:E.
         - apply Nat.eqb_eq in E. subst. exfalso. apply HYT0. assumption.
         - reflexivity. }
    exact HIH.
  - (* Nat *) simpl. constructor.
Qed.

Lemma open_ty_subst_fresh_rec : forall T X U j, ~ In X (ty_fvars T) ->
  ty_subst X U (open_ty_rec j (Ty_FVar X) T) = open_ty_rec j U T.
Proof.
  induction T as [n | Y | T1 IH1 T2 IH2 | T1 IH1 | ]; intros X U j Hfresh; simpl.
  - (* BVar *) destruct (Nat.eqb j n) eqn:E; simpl.
    + rewrite Nat.eqb_refl. reflexivity.
    + reflexivity.
  - (* FVar Y *) simpl in Hfresh. assert (Hne : Y <> X) by (intro Hc; apply Hfresh; subst; auto).
    destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hne. symmetry. exact E.
    + reflexivity.
  - (* Arrow *) simpl in Hfresh. f_equal.
    + apply IH1. intro Hc. apply Hfresh. apply in_app_iff. left. assumption.
    + apply IH2. intro Hc. apply Hfresh. apply in_app_iff. right. assumption.
  - (* All *) f_equal. apply IH1. assumption.
  - (* Nat *) reflexivity.
Qed.

Lemma open_ty_subst_fresh : forall T X U, ~ In X (ty_fvars T) ->
  ty_subst X U (open_ty T (Ty_FVar X)) = open_ty T U.
Proof. intros T X U H. apply open_ty_subst_fresh_rec. assumption. Qed.

Lemma wf_ty_open : forall Delta T U, wf_ty Delta (Ty_All T) -> wf_ty Delta U -> wf_ty Delta (open_ty T U).
Proof.
  intros Delta T U HAll HU.
  inversion HAll as [| |L Delta0 T0 Hbody|]; subst.
  set (X := fresh_atom (L ++ ty_fvars T)).
  assert (HXnot : ~ In X (L ++ ty_fvars T)) by apply fresh_atom_notin.
  assert (HXL : ~ In X L) by (apply not_in_app_l with (l2 := ty_fvars T); assumption).
  assert (HXT : ~ In X (ty_fvars T)) by (apply not_in_app_r with (l1 := L); assumption).
  pose proof (Hbody X HXL) as Hw.
  rewrite <- (open_ty_subst_fresh T X U HXT).
  rewrite ty_subst_env_single.
  apply wf_ty_subst_env with (D := X :: Delta) (D' := Delta).
  - exact Hw.
  - intros Y HY. simpl in HY. destruct (Nat.eqb X Y) eqn:E.
    + apply Nat.eqb_eq in E. subst. exact HU.
    + apply Nat.eqb_neq in E. apply WF_Var.
      destruct HY as [HYX|HYD].
      * exfalso. apply E. exact HYX.
      * assumption.
  - intro Y. destruct (Nat.eqb X Y) eqn:E.
    + apply wf_ty_lc in HU. assumption.
    + constructor.
Qed.


(* ---------------------------------------------------------------- *)
(* Inversion lemmas for well-formed types                           *)
(* ---------------------------------------------------------------- *)

Lemma wf_ty_arrow_inv : forall D T1 T2, wf_ty D (Ty_Arrow T1 T2) -> wf_ty D T1 /\ wf_ty D T2.
Proof. intros D T1 T2 H. inversion H; subst; split; assumption. Qed.

Lemma wf_ty_all_inv : forall D T, wf_ty D (Ty_All T) ->
  exists L, forall X, ~ In X L -> wf_ty (X :: D) (open_ty T (Ty_FVar X)).
Proof. intros D T H. inversion H; subst. exists L. assumption. Qed.

(* ---------------------------------------------------------------- *)
(* Typed terms are well-formed and locally closed                   *)
(* ---------------------------------------------------------------- *)

Lemma has_type_wf : forall Delta Gamma t T, has_type Delta Gamma t T -> wf_ty Delta T.
Proof.
  intros Delta Gamma t T H.
  induction H as [Delta0 Gamma0 x T0 Hlook Hwf
                 | L Delta0 Gamma0 T1 t2 T2 HwfT1 Hfun IHfun
                 | Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta0 Gamma0 t T Hfun IHfun
                 | Delta0 Gamma0 t T U H1 IH1 HwfU
                 | Delta0 Gamma0
                 | Delta0 Gamma0 n H1 IH1
                 | Delta0 Gamma0 n b s T H1 IH1 H2 IH2 H3 IH3].
  - (* Var *) exact Hwf.
  - (* Abs *) constructor.
    + exact HwfT1.
    + pose (x := fresh_atom L).
      apply (IHfun x). apply fresh_atom_notin.
  - (* App *) apply wf_ty_arrow_inv in IH1. destruct IH1 as [Hf Ht]. exact Ht.
  - (* TAbs *) apply WF_All with (L := L). intros X HX.
    apply IHfun. assumption.
  - (* TApp *) apply wf_ty_open with (T := T); assumption.
  - (* Zero *) constructor.
  - (* Succ *) exact IH1.
  - (* Rec *) exact IH2.
Qed.

Lemma has_type_lc : forall Delta Gamma t T, has_type Delta Gamma t T -> lc_tm_at 0 0 t.
Proof.
  intros Delta Gamma t T H.
  induction H as [Delta0 Gamma0 x T0 Hlook Hwf
                 | L Delta0 Gamma0 T1 t2 T2 HwfT1 Hfun IHfun
                 | Delta0 Gamma0 t1 t2 T1 T2 H1 IH1 H2 IH2
                 | L Delta0 Gamma0 t T Hfun IHfun
                 | Delta0 Gamma0 t T U H1 IH1 HwfU
                 | Delta0 Gamma0
                 | Delta0 Gamma0 n H1 IH1
                 | Delta0 Gamma0 n b s T H1 IH1 H2 IH2 H3 IH3].
  - (* Var *) constructor.
  - (* Abs *) constructor.
    + apply (wf_ty_lc Delta0 T1 HwfT1).
    + pose (x := fresh_atom L).
      pose proof (IHfun x (fresh_atom_notin L)) as Hopen.
      unfold open_tm in Hopen.
      exact (lc_tm_open_inv t2 0 0 0 (tm_fvar x) (Nat.le_refl 0) Hopen (lc_tm_fvar 0 0 x)).
  - (* App *) constructor; assumption.
  - (* TAbs *) constructor.
    pose (X := fresh_atom L).
    pose proof (IHfun X (fresh_atom_notin L)) as Hopen.
    unfold open_tm_ty in Hopen.
    exact (lc_open_tm_ty_inv t 0 0 (Ty_FVar X) Hopen).
  - (* TApp *) constructor.
    + assumption.
    + apply (wf_ty_lc Delta0 U HwfU).
  - (* Zero *) constructor.
  - (* Succ *) constructor. assumption.
  - (* Rec *) constructor; assumption.
Qed.


(* ---------------------------------------------------------------- *)
(* The unary logical relation                                       *)
(* ---------------------------------------------------------------- *)

Definition Cand := tm -> Prop.

Definition good_cand (C : Cand) : Prop :=
  (forall t, C t -> strongly_normalizing t) /\
  (forall t, C t -> lc_tm_at 0 0 t) /\
  (forall t, C t -> erase t = t) /\
  (forall t t', C t -> t --> t' -> C t') /\
  (forall t, strongly_normalizing t -> lc_tm_at 0 0 t -> erase t = t -> ~ value t ->
             (forall t', t --> t' -> C t') -> C t).

Lemma good_cand_sn : forall C, good_cand C -> forall t, C t -> strongly_normalizing t.
Proof. intros C [H1 [H2 [H3 [H4 H5]]]] t Ht. apply H1. assumption. Qed.

Lemma good_cand_lc : forall C, good_cand C -> forall t, C t -> lc_tm_at 0 0 t.
Proof. intros C [H1 [H2 [H3 [H4 H5]]]] t Ht. apply H2. assumption. Qed.

Lemma good_cand_E : forall C, good_cand C -> forall t, C t -> erase t = t.
Proof. intros C [H1 [H2 [H3 [H4 H5]]]] t Ht. apply H3. assumption. Qed.

Lemma good_cand_step : forall C, good_cand C -> forall t t', C t -> t --> t' -> C t'.
Proof. intros C [H1 [H2 [H3 [H4 H5]]]] t t' Ht Hs. apply (H4 t t'); assumption. Qed.

Lemma good_cand_expand : forall C, good_cand C -> forall t,
  strongly_normalizing t -> lc_tm_at 0 0 t -> erase t = t -> ~ value t ->
  (forall t', t --> t' -> C t') -> C t.
Proof. intros C [H1 [H2 [H3 [H4 H5]]]] t Ha Hb Hc Hd He. apply H5; assumption. Qed.

Definition env_good (env : list Cand) : Prop := forall C, In C env -> good_cand C.

Definition xi_good (xi : atom -> Cand) : Prop := forall X, good_cand (xi X).

Definition top_cand : Cand := fun t => strongly_normalizing t /\ lc_tm_at 0 0 t /\ erase t = t.

Definition nth_cand (env : list Cand) (i : nat) : Cand :=
  match nth_error env i with Some C => C | None => top_cand end.

Definition xi_upd (xi : atom -> Cand) (X : atom) (C : Cand) : atom -> Cand :=
  fun Y => if Nat.eqb X Y then C else xi Y.

Lemma xi_upd_eq : forall xi X C, xi_upd xi X C X = C.
Proof. intros. unfold xi_upd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma xi_upd_neq : forall xi X Y C, X <> Y -> xi_upd xi X C Y = xi Y.
Proof.
  intros. unfold xi_upd. destruct (Nat.eqb X Y) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Fixpoint R (env : list Cand) (xi : atom -> Cand) (T : ty) : Cand :=
  match T with
  | Ty_BVar i => nth_cand env i
  | Ty_FVar X => xi X
  | Ty_Nat => fun t => strongly_normalizing t /\ lc_tm_at 0 0 t /\ erase t = t /\
                        (forall v, multi t v -> value v -> numeric_value v)
  | Ty_Arrow T1 T2 => fun t => strongly_normalizing t /\ lc_tm_at 0 0 t /\ erase t = t /\
                        (forall u, R env xi T1 u -> R env xi T2 (tm_app t u))
  | Ty_All T1 => fun t => strongly_normalizing t /\ lc_tm_at 0 0 t /\ erase t = t /\
                        (forall C, good_cand C -> R (C :: env) xi T1 (tm_tapp t Ty_Nat))
  end.


Lemma top_cand_good : good_cand top_cand.
Proof.
  unfold good_cand. repeat split.
  - intros t Ht. exact (proj1 Ht).
  - intros t Ht. exact (proj1 (proj2 Ht)).
  - intros t Ht. exact (proj2 (proj2 Ht)).
  - intros t t' Ht Hstep. destruct Ht as [Hsn [Hlc HE]].
    split; [|split].
    + eapply SN_step; eassumption.
    + eapply lc_step; eassumption.
    + unfold E in *. rewrite <- HE. apply step_erase. assumption.
  - intros t Hsn Hlc HE Hnv Hall. split; [|split]; assumption.
Qed.

Lemma nth_cand_good : forall env i, env_good env -> good_cand (nth_cand env i).
Proof.
  intros env i Hge. unfold nth_cand. destruct (nth_error env i) as [C|] eqn:E.
  - apply Hge. apply nth_error_In. exact E.
  - apply top_cand_good.
Qed.

Lemma R_nat_destruct : forall env xi t, R env xi Ty_Nat t ->
  strongly_normalizing t /\ lc_tm_at 0 0 t /\ erase t = t /\
  (forall v, multi t v -> value v -> numeric_value v).
Proof. intros env xi t H. cbn [R] in H. exact H. Qed.

Lemma R_nat_intro : forall env xi t,
  strongly_normalizing t -> lc_tm_at 0 0 t -> erase t = t ->
  (forall v, multi t v -> value v -> numeric_value v) -> R env xi Ty_Nat t.
Proof. intros env xi t H1 H2 H3 H4. cbn [R]. repeat split; assumption. Qed.

Lemma R_arrow_destruct : forall env xi T1 T2 t, R env xi (Ty_Arrow T1 T2) t ->
  strongly_normalizing t /\ lc_tm_at 0 0 t /\ erase t = t /\
  (forall u, R env xi T1 u -> R env xi T2 (tm_app t u)).
Proof. intros env xi T1 T2 t H. cbn [R] in H. exact H. Qed.

Lemma R_arrow_intro : forall env xi T1 T2 t,
  strongly_normalizing t -> lc_tm_at 0 0 t -> erase t = t ->
  (forall u, R env xi T1 u -> R env xi T2 (tm_app t u)) -> R env xi (Ty_Arrow T1 T2) t.
Proof. intros env xi T1 T2 t H1 H2 H3 H4. cbn [R]. repeat split; assumption. Qed.

Lemma R_all_destruct : forall env xi T1 t, R env xi (Ty_All T1) t ->
  strongly_normalizing t /\ lc_tm_at 0 0 t /\ erase t = t /\
  (forall C, good_cand C -> R (C :: env) xi T1 (tm_tapp t Ty_Nat)).
Proof. intros env xi T1 t H. cbn [R] in H. exact H. Qed.

Lemma R_all_intro : forall env xi T1 t,
  strongly_normalizing t -> lc_tm_at 0 0 t -> erase t = t ->
  (forall C, good_cand C -> R (C :: env) xi T1 (tm_tapp t Ty_Nat)) -> R env xi (Ty_All T1) t.
Proof. intros env xi T1 t H1 H2 H3 H4. cbn [R]. repeat split; assumption. Qed.

Lemma R_sn : forall T env xi t, env_good env -> xi_good xi -> R env xi T t -> strongly_normalizing t.
Proof.
  induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1 | ]; intros env xi t Hge Hgi HR.
  - (* BVar *) apply (good_cand_sn (nth_cand env i)); [apply nth_cand_good; assumption|exact HR].
  - (* FVar *) apply (good_cand_sn (xi X)); [apply Hgi|exact HR].
  - (* Arrow *) apply R_arrow_destruct in HR. exact (proj1 HR).
  - (* All *) apply R_all_destruct in HR. exact (proj1 HR).
  - (* Nat *) apply R_nat_destruct in HR. exact (proj1 HR).
Qed.

Lemma R_lc : forall T env xi t, env_good env -> xi_good xi -> R env xi T t -> lc_tm_at 0 0 t.
Proof.
  induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1 | ]; intros env xi t Hge Hgi HR.
  - (* BVar *) apply (good_cand_lc (nth_cand env i)); [apply nth_cand_good; assumption|exact HR].
  - (* FVar *) apply (good_cand_lc (xi X)); [apply Hgi|exact HR].
  - (* Arrow *) apply R_arrow_destruct in HR. exact (proj1 (proj2 HR)).
  - (* All *) apply R_all_destruct in HR. exact (proj1 (proj2 HR)).
  - (* Nat *) apply R_nat_destruct in HR. exact (proj1 (proj2 HR)).
Qed.

Lemma R_E : forall T env xi t, env_good env -> xi_good xi -> R env xi T t -> erase t = t.
Proof.
  induction T as [i | X | T1 IH1 T2 IH2 | T1 IH1 | ]; intros env xi t Hge Hgi HR.
  - (* BVar *) apply (good_cand_E (nth_cand env i)); [apply nth_cand_good; assumption|exact HR].
  - (* FVar *) apply (good_cand_E (xi X)); [apply Hgi|exact HR].
  - (* Arrow *) apply R_arrow_destruct in HR. exact (proj1 (proj2 (proj2 HR))).
  - (* All *) apply R_all_destruct in HR. exact (proj1 (proj2 (proj2 HR))).
  - (* Nat *) apply R_nat_destruct in HR. exact (proj1 (proj2 (proj2 HR))).
Qed.

Lemma R_nat_multi : forall env xi t, R env xi Ty_Nat t ->
  forall v, multi t v -> value v -> numeric_value v.
Proof. intros env xi t H. apply R_nat_destruct in H. exact (proj2 (proj2 (proj2 H))). Qed.

Lemma R_arrow_elim : forall env xi T1 T2 t, R env xi (Ty_Arrow T1 T2) t ->
  forall u, R env xi T1 u -> R env xi T2 (tm_app t u).
Proof. intros env xi T1 T2 t H. apply R_arrow_destruct in H. exact (proj2 (proj2 (proj2 H))). Qed.

Lemma R_all_elim : forall env xi T1 t, R env xi (Ty_All T1) t ->
  forall C, good_cand C -> R (C :: env) xi T1 (tm_tapp t Ty_Nat).
Proof. intros env xi T1 t H. apply R_all_destruct in H. exact (proj2 (proj2 (proj2 H))). Qed.

Theorem normalization : forall t T,
  has_type [] empty t T -> strongly_normalizing t.
Proof.
  (* Complete the proof of normalization. *)
Qed.

End SystemFNormalizationRecursionHardTask.
